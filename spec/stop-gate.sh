#!/bin/bash
# Claude Code の Stop フック：応答を終える前に spec/check.sh --quick を走らせ、通らなければ終わらせずに差し戻す。
# Lean の変更がない（前回通ったときと同じ）なら走らせない。差し戻しは1回まで（stop_hook_active）。
ROOT=$(cd "$(dirname "$0")/.." && pwd)
cd "$ROOT"
input=$(cat)
if echo "$input" | grep -q '"stop_hook_active": *true'; then exit 0; fi

key=$( { git rev-parse HEAD; git diff HEAD -- '*.lean' lakefile.toml lean-toolchain;
         git ls-files --others --exclude-standard -- '*.lean' | xargs -r cat; } 2>/dev/null | sha256sum | cut -d' ' -f1)
stamp="$ROOT/.lake/spec-gate-ok"
[ -f "$stamp" ] && [ "$(cat "$stamp")" = "$key" ] && exit 0

if out=$(spec/check.sh --quick 2>&1); then
  mkdir -p "$ROOT/.lake" && echo "$key" > "$stamp"
  exit 0
fi
{
  echo "証明のゲート（spec/check.sh --quick）に通りません。直してから終えてください。"
  echo "通らないまま終えるなら、「証明済み」とは報告せず、通らない理由を報告してください。"
  echo "$out" | tail -30
} >&2
exit 2
