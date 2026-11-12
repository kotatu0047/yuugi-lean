#!/usr/bin/env python3
"""Claude Code の PreToolUse フック（Bash）：守るファイルを書き換えそうなコマンドを止める。

settings.json の permissions.deny は Edit・Write ツールにしか効かず、sed -i やリダイレクトでは書き換えられるので、
その穴をふさぐ。コマンドの文面から推測するだけなので完全ではない（最後の防御は CI とレビュー）。
"""
import json
import re
import sys

# 守るファイル・ディレクトリ。前後に名前の続き（英数字・_・.・-）がないときだけ当たる
# （spec なら spec と spec/… に当たり、inspect や spec.md には当たらない）
PROTECTED = [
    r"(?<![\w.-])" + p + r"(?![\w.-])"
    for p in [
        r"spec",
        r"\.claude/settings(?:\.local)?\.json",
        r"\.claude/hooks",
        r"\.github/workflows",
        r"\.githooks",
        r"tools/check-all\.sh",
        r"jobs/accept\.py",
        r"lakefile\.toml",
        r"lean-toolchain",
    ]
]
# 守るファイルを使うだけのコマンド（読む・実行する）。コマンドの先頭（; & | の後も）にあるときだけ外す。
# 引数の位置（git checkout -- tools/check-all.sh など）や書き込み先（> spec/check.sh）にあるときは外さない。
ALLOWED = [
    r"spec/check\.sh(\s+--quick)?",
    r"python3\s+spec/(scan|report_names)\.py",
    r"python3\s+jobs/accept\.py\s+(--recheck|jobs/pending/\d+)",
    r"tools/check-all\.sh(\s+--no-unity)?",
]
# 何も書き換えないリダイレクト
HARMLESS = [r"\d*>&\d", r"&?\d*>\s*/dev/null"]
WRITE = [
    r">", r"\btee\b", r"\bsed\b[^|;&]*\s-i", r"\bperl\b[^|;&]*\s-[a-z]*i", r"\bmv\b", r"\bcp\b", r"\brm\b",
    r"\bln\b", r"\bchmod\b", r"\btruncate\b", r"\bdd\b", r"\binstall\b", r"\btouch\b", r"\bpython3?\b", r"\bnode\b",
    r"\bgit\s+(checkout|restore|reset|apply|am|stash|mv|rm|revert|cherry-pick|merge|rebase|pull)\b", r"\bpatch\b",
]

cmd = json.load(sys.stdin).get("tool_input", {}).get("command", "")
rest = cmd
for a in HARMLESS:
    rest = re.sub(a, " ", rest)
for a in ALLOWED:
    rest = re.sub(r"(^|[;&|(])\s*" + a + r"(?=\s|$|[;&|)])", r"\1 ", rest)
if any(re.search(p, rest) for p in PROTECTED) and any(re.search(w, rest) for w in WRITE):
    print("守るファイル（spec/・ゲートのスクリプト・設定・CI）を書き換えうるコマンドは実行できません。"
          "変更が必要なら、案をユーザーに示して頼んでください（CLAUDE.md）。", file=sys.stderr)
    sys.exit(2)
