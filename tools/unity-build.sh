#!/bin/bash
# WSL のリポジトリの作業中のファイルを Windows 側のクローンに写し、Unity でビルドする。
#
#   tools/unity-build.sh                     写してビルドする
#   tools/unity-build.sh --reset             先に Windows 側のクローンの変更を捨てて git pull する
#   tools/unity-build.sh --test              写して、エディタと画面の自動テスト（EditMode）を動かす（ビルドはしない）
#   tools/unity-build.sh --shot 画面.png [exe の引数…]
#                                            ビルドしたアプリを動かして画面を保存する（例：-cardgen-play 7）
#
# Unity は WSL のファイルシステム上のプロジェクトを開けない（大文字小文字を区別するため）ので、
# Windows 側にもう1つクローンを置き、そこでビルドする。Windows 側は「ビルド用の写し」として扱い、
# 編集は WSL 側で行う（写すときに Windows 側の同じファイルは上書きされる）。
#
# 環境変数で変えられるもの：
#   CARDGEN_WIN_REPO  Windows 側のクローン（既定：Windows のユーザーフォルダの repo/yuugi-lean）
#   CARDGEN_UNITY     Unity.exe（既定：Unity Hub の、ProjectVersion.txt の版）
set -euo pipefail

SRC=$(cd "$(dirname "$0")/.." && pwd)
PROJ_REL=unity/CardGenEditor
VERSION=$(sed -n 's/^m_EditorVersion: //p' "$SRC/$PROJ_REL/ProjectSettings/ProjectVersion.txt")
WIN_HOME=$(wslpath "$(cmd.exe /c 'echo %USERPROFILE%' 2>/dev/null | tr -d '\r')")
DST=${CARDGEN_WIN_REPO:-$WIN_HOME/repo/yuugi-lean}
UNITY=${CARDGEN_UNITY:-"/mnt/c/Program Files/Unity/Hub/Editor/$VERSION/Editor/Unity.exe"}

reset=0
shot=""
test=0
while [ $# -gt 0 ]; do
  case "$1" in
    --reset) reset=1; shift ;;
    --test) test=1; shift ;;
    --shot) shot=$2; shift 2; break ;;
    *) echo "不明な引数：$1" >&2; exit 2 ;;
  esac
done

if [ ! -d "$DST/.git" ]; then
  echo "Windows 側のクローンがありません：$DST" >&2
  echo "例：git clone $(git -C "$SRC" remote get-url origin) \"$DST\"" >&2
  exit 1
fi

if [ $reset = 1 ]; then
  echo "== Windows 側のクローンの変更を捨てて最新にする"
  git -C "$DST" checkout -- .
  git -C "$DST" clean -fdq -- csharp "$PROJ_REL/Assets" "$PROJ_REL/Packages"
  git -C "$DST" pull --ff-only -q
fi

echo "== 写す：$SRC → $DST"
rsync -a "$SRC/csharp/CardGen.Core/" "$DST/csharp/CardGen.Core/"
rsync -a "$SRC/$PROJ_REL/Assets/" "$DST/$PROJ_REL/Assets/"
rsync -a "$SRC/$PROJ_REL/Packages/manifest.json" "$DST/$PROJ_REL/Packages/manifest.json"

if [ $test = 1 ]; then
  echo "== テスト（Unity $VERSION・EditMode）"
  RES="$DST/$PROJ_REL/Logs/cardgen-tests.xml"
  TLOG="$DST/$PROJ_REL/Logs/cardgen-tests.log"
  rm -f "$RES"
  (cd "$DST/$PROJ_REL" && "$UNITY" -batchmode -nographics -projectPath . -runTests -testPlatform EditMode \
     -testResults "$(wslpath -w "$RES")" -logFile "$(wslpath -w "$TLOG")") >/dev/null || true
  # Unity が書き換えた packages-lock.json を WSL 側に戻す（パッケージを加えたとき）
  cp "$DST/$PROJ_REL/Packages/packages-lock.json" "$SRC/$PROJ_REL/Packages/packages-lock.json"
  if [ ! -f "$RES" ]; then
    grep -E "error CS|Exception" "$TLOG" | head -20 >&2 || true
    echo "テストを動かせませんでした。ログ：$TLOG" >&2
    exit 1
  fi
  python3 - "$RES" <<'PY'
import sys, xml.etree.ElementTree as ET
root = ET.parse(sys.argv[1]).getroot()
print(f"合計 {root.get('total')}・成功 {root.get('passed')}・失敗 {root.get('failed')}・スキップ {root.get('skipped')}")
for tc in root.iter("test-case"):
    mark = {"Passed": "○", "Failed": "×"}.get(tc.get("result"), "－")
    print(f"  {mark} {tc.get('fullname')}")
    if tc.get("result") == "Failed":
        msg = tc.find("failure/message")
        if msg is not None and msg.text: print("      " + msg.text.strip().replace("\n", "\n      ")[:800])
sys.exit(0 if root.get("result", "").startswith("Passed") else 2)
PY
  exit $?
fi

echo "== ビルド（Unity $VERSION）"
LOG="$DST/$PROJ_REL/Logs/cardgen-build.log"
mkdir -p "$(dirname "$LOG")"
# Unity は作業ディレクトリをパスにつなげてしまうので、プロジェクトの中から「.」で開く
(cd "$DST/$PROJ_REL" && "$UNITY" -batchmode -nographics -projectPath . \
   -executeMethod CardGen.App.EditorTools.CardGenBuild.BuildWindows -quit -logFile "$(wslpath -w "$LOG")") >/dev/null || true
if ! grep -q "CardGen build: Succeeded" "$LOG"; then
  grep -E "error CS|CardGen build" "$LOG" >&2 || true
  echo "ビルドに失敗しました。ログ：$LOG" >&2
  exit 1
fi
echo "成功：$DST/$PROJ_REL/Build/CardGenEditor.exe"

if [ -n "$shot" ]; then
  echo "== 画面を保存：$shot"
  TMP_PNG="$DST/$PROJ_REL/Logs/cardgen-shot.png"
  rm -f "$TMP_PNG"
  (cd "$DST/$PROJ_REL/Build" && timeout 180 ./CardGenEditor.exe -screen-width 1600 -screen-height 1000 -screen-fullscreen 0 \
     "$@" -cardgen-screenshot "$(wslpath -w "$TMP_PNG")" -logFile "$(wslpath -w "$DST/$PROJ_REL/Logs/cardgen-player.log")") >/dev/null || true
  if [ ! -f "$TMP_PNG" ]; then echo "画面を保存できませんでした" >&2; exit 1; fi
  cp "$TMP_PNG" "$shot"
fi
