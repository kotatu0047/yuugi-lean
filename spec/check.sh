#!/bin/bash
# 証明のゲート：これが通ることだけを「証明済み」とする（ビルドが通った補題の本数は進捗ではない）。
#
#   spec/check.sh          すべて（CI とコミット前のフックから）
#   spec/check.sh --quick  カーネルでの再検査と、証明ジョブの再検査を飛ばす（Claude Code の Stop フックから）
#
# 1. lake build：CardGen・検査ツール・Spec（凍結した主張との型の一致と、公理が標準の3つだけであること）
# 2. CardGen のソースに sorry・axiom・native_decide などがないこと
# 3. レポートが名前を出す定理が、どれも Spec で検査されていること
# 4. leanchecker：.olean をカーネルで検査し直す（メタプログラムで環境を書き換える手を弾く）
# 5. 受け入れ済みの証明ジョブの再検査
set -uo pipefail

ROOT=$(cd "$(dirname "$0")/.." && pwd)
cd "$ROOT"
export PATH="$HOME/.elan/bin:$PATH"

quick=0
[ "${1:-}" = "--quick" ] && quick=1

fail() { echo "× ゲートに通りません：$1" >&2; exit 1; }

lake build CardGen cardgen Spec >/dev/null 2>&1 || {
  lake build CardGen cardgen Spec 2>&1 | grep -E "error|sorry" | head -20 >&2
  fail "lake build（主張の不一致・許可していない公理・ビルドの誤り）"
}
echo "○ ビルドと、凍結した主張・公理の検査"
python3 spec/scan.py || fail "禁止した書き方"
python3 spec/report_names.py || fail "検査していない定理をレポートが出している"
if [ $quick = 0 ]; then
  lake env leanchecker CardGen Spec || fail "leanchecker（カーネルでの再検査）"
  echo "○ カーネルでの再検査（leanchecker）"
  python3 jobs/accept.py --recheck || fail "証明ジョブの再検査"
fi
echo "== ゲートを通りました"
