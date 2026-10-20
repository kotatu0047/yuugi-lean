#!/usr/bin/env python3
"""Claude Code の PreToolUse フック（Bash）：守るファイルを書き換えそうなコマンドを止める。

settings.json の permissions.deny は Edit・Write ツールにしか効かず、sed -i やリダイレクトでは書き換えられるので、
その穴をふさぐ。コマンドの文面から推測するだけなので完全ではない（最後の防御は CI とレビュー）。
"""
import json
import re
import sys

PROTECTED = [
    r"spec/",
    r"\.claude/settings",
    r"\.claude/hooks",
    r"\.github/workflows",
    r"\.githooks",
    r"tools/check-all\.sh",
    r"jobs/accept\.py",
    r"lakefile\.toml",
    r"lean-toolchain",
]
# 守るファイルを使うだけのコマンド（読む・実行する）
ALLOWED = [
    r"spec/check\.sh(\s+--quick)?",
    r"python3\s+spec/(scan|report_names)\.py",
    r"python3\s+jobs/accept\.py\s+(--recheck|jobs/pending/\d+)",
    r"tools/check-all\.sh(\s+--no-unity)?",
]
WRITE = [
    r">", r"\btee\b", r"\bsed\b[^|;&]*\s-i", r"\bperl\b[^|;&]*\s-[a-z]*i", r"\bmv\b", r"\bcp\b", r"\brm\b",
    r"\bln\b", r"\bchmod\b", r"\btruncate\b", r"\bdd\b", r"\binstall\b", r"\btouch\b", r"\bpython3?\b", r"\bnode\b",
    r"\bgit\s+(checkout|restore|reset|apply|am|stash|mv|rm|revert|cherry-pick|merge|rebase|pull)\b", r"\bpatch\b",
]

cmd = json.load(sys.stdin).get("tool_input", {}).get("command", "")
rest = cmd
for a in ALLOWED:
    rest = re.sub(a, " ", rest)
if any(re.search(p, rest) for p in PROTECTED) and any(re.search(w, rest) for w in WRITE):
    print("守るファイル（spec/・ゲートのスクリプト・設定・CI）を書き換えうるコマンドは実行できません。"
          "変更が必要なら、案をユーザーに示して頼んでください（CLAUDE.md）。", file=sys.stderr)
    sys.exit(2)
