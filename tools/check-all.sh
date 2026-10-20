#!/bin/bash
# YuugiLean 以外のすべてのビルドとテストを順に実行する。コミット前のフック（.githooks/pre-commit）からも呼ばれる。
#
#   tools/check-all.sh            すべて実行する
#   tools/check-all.sh --no-unity Unity のビルドとテストを飛ばす（Windows 側が使えないとき）
#
# 途中で1つでも失敗したら、そこで止めて終了コード 1 を返す。
# Unity は Windows 側の同じクローンを使うので、同時に2つ動かないようにロックをかける。
set -uo pipefail

ROOT=$(cd "$(dirname "$0")/.." && pwd)
cd "$ROOT"
export PATH="$HOME/.elan/bin:$HOME/.dotnet:$PATH"
export DOTNET_ROOT="${DOTNET_ROOT:-$HOME/.dotnet}"

unity=1
[ "${1:-}" = "--no-unity" ] && unity=0

mkdir -p "$ROOT/.lake"
exec 9>"$ROOT/.lake/check-all.lock"
if ! flock -n 9; then
  echo "== ほかの check-all.sh が終わるのを待つ"
  flock 9
fi

start=$(date +%s)
step() {
  local name=$1; shift
  local t0=$(date +%s)
  echo "== $name"
  if ! "$@"; then
    echo "× 失敗：$name" >&2
    exit 1
  fi
  echo "○ $name（$(( $(date +%s) - t0 )) 秒）"
}

# Lean：CardGen と検査ツール。#guard のテストと、vectors.json が最新かの確認（VectorsCheck）も含む
step "Lean のビルド（lake build）" lake build
step "証明ジョブの再検査" python3 jobs/accept.py --recheck
step "C# のテスト（dotnet test）" bash -c "cd csharp/CardGen.Tests && dotnet test --nologo -v q"
step "ドキュメントのサイト（mkdocs build --strict）" bash -c "python3 tools/docs-site.py >/dev/null && mkdocs build --strict -q"
if [ $unity = 1 ]; then
  step "Unity の画面の自動テスト" tools/unity-build.sh --test
  # --rclick はアプリのビルドもする
  step "Unity のビルドと右クリック・ドラッグの確認" tools/unity-build.sh --rclick
fi

echo "== すべて成功（$(( $(date +%s) - start )) 秒）"
