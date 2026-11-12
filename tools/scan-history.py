#!/usr/bin/env python3
"""会話記録（.claude-history/）に、秘密の情報らしい文字列がないか調べる。

    tools/scan-history.py          ステージした .claude-history/ の差分で、足された行だけを調べる
    tools/scan-history.py --all    .claude-history/ の全ファイルを調べる

見つかったら「ファイル:行  種類  伏せた値」を出して終了コード 1 を返す。
値は先頭だけ残して伏せる（この出力自体が会話記録に残るため）。
機械で拾うのは候補だけで、本物かどうかはエージェントが該当の行を読んで判断する（CLAUDE.md）。
"""
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
HISTORY = ".claude-history"

PATTERNS = [
    ("秘密鍵", re.compile(r"-----BEGIN [A-Z ]*PRIVATE KEY-----")),
    ("GitHub のトークン", re.compile(r"\b(?:gh[pousr]_[A-Za-z0-9]{20,}|github_pat_[A-Za-z0-9_]{20,})")),
    ("Anthropic/OpenAI のキー", re.compile(r"\bsk-(?:ant-)?[A-Za-z0-9_-]{20,}")),
    ("AWS のキー", re.compile(r"\b(?:AKIA|ASIA)[A-Z0-9]{16}\b")),
    ("Google の API キー", re.compile(r"\bAIza[0-9A-Za-z_-]{30,}")),
    ("Slack のトークン", re.compile(r"\bxox[abprs]-[A-Za-z0-9-]{10,}")),
    ("JWT", re.compile(r"\beyJ[A-Za-z0-9_-]{10,}\.[A-Za-z0-9_-]{10,}\.[A-Za-z0-9_-]{10,}")),
    ("認証つき URL", re.compile(r"\b[a-z][a-z0-9+.-]*://[^/\s:@]+:[^/\s@]+@")),
    ("パスワードらしい代入", re.compile(
        r"(?i)\b(?:password|passwd|pwd|secret|token|api[_-]?key)\b\s*[:=]\s*['\"]?[^\s'\"`]{6,}")),
    ("メールアドレス", re.compile(r"\b[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}\b")),
]

# 公開してよいと分かっているもの
ALLOW = [
    re.compile(r"noreply@anthropic\.com"),
    re.compile(r"@(?:example\.(?:com|org|net)|users\.noreply\.github\.com)\b"),
]


def mask(s: str) -> str:
    keep = min(4, len(s) // 4)
    return s[:keep] + "…" + f"（{len(s)} 文字）"


def staged_lines():
    diff = subprocess.run(
        ["git", "diff", "--cached", "-U0", "--no-color", "--", HISTORY],
        cwd=ROOT, capture_output=True, text=True, check=True).stdout
    path, lineno = None, 0
    for line in diff.splitlines():
        if line.startswith("+++ "):
            path = line[6:] if line.startswith("+++ b/") else None
        elif line.startswith("@@"):
            m = re.search(r"\+(\d+)", line)
            lineno = int(m.group(1)) if m else 0
        elif line.startswith("+") and path:
            yield path, lineno, line[1:]
            lineno += 1


def all_lines():
    for p in sorted((ROOT / HISTORY).glob("*.md")):
        rel = p.relative_to(ROOT).as_posix()
        for i, line in enumerate(p.read_text(encoding="utf-8").splitlines(), 1):
            yield rel, i, line


def main():
    lines = all_lines() if "--all" in sys.argv[1:] else staged_lines()
    hits = 0
    for path, lineno, text in lines:
        for kind, pat in PATTERNS:
            for m in pat.finditer(text):
                if any(a.search(m.group(0)) for a in ALLOW):
                    continue
                print(f"{path}:{lineno}  {kind}  {mask(m.group(0))}")
                hits += 1
    if hits:
        print(f"== 候補が {hits} 件。該当の行を読んで、本物の秘密かどうか判断する")
        return 1
    print("== 秘密の情報らしい文字列は見つからない")
    return 0


if __name__ == "__main__":
    sys.exit(main())
