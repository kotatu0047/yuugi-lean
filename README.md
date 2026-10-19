# yuugi-lean

ドキュメントは Web でも読める：https://kotatu0047.github.io/yuugi-lean/ （`master` に push するたびに GitHub Actions で作り直す。手元で見るなら `python3 tools/docs-site.py && mkdocs serve`。必要なのは `pip install mkdocs-material`）

遊戯王 OCG のルールの Lean 4 による形式化と、それを土台にした「検証付きカードゲームジェネレーター」の検査部分。

## YuugiLean：遊戯王 OCG のルールの形式化

- `YuugiLean/YuGiOh.lean`：ルール・チェーン・永続効果の判定・カードの効果
- `YuugiLean/Invariants.lean` ほか：カードの総数・uid・ゾーンの上限・ターンプレイヤーなどの不変条件の証明
- `YuugiLean/Quad.lean`：スキルドレイン・王宮のお触れ・人造人間－サイコ・ショッカー・D－HERO Bloo－D の「4すくみ」の解析（考察は `4すくみ考察.md`）

## CardGen：検証付きカードゲームジェネレーターの検査

ユーザーがビジュアルエディタで作ったルールとカード（中間表現の JSON）を検査する。企画は `企画書.md`、構成と処理の流れの図は `アーキテクチャ.md`、まだ実装していないアイデアは `アイデア.md`。

- `CardGen/IR.lean`：中間表現（説明は `CardGen/中間表現.md`、見本は `CardGen/sample.json`）
- `CardGen/Model.lean`・`CardGen/Inv.lean`：対戦のモデル（遊戯王式と MTG 式の戦闘、カードに残るダメージ）と、どの盤面でも成り立つ盤面の制約
- `CardGen/Play.lean`：実行できる対戦の1歩と、それが証明に使う動きの関係と一致すること（`step?_sound`）
- `CardGen/Claims.lean`：ルールから導く性質（★）と、それがすべての対戦で成り立つことの証明（`derived_valid`）
- `CardGen/Negation.lean`：無効の関係に循環がなければ判定が必ず止まり結果が1通りであることの証明（`negation_settles`）
- `CardGen/Pool.lean`：盤面のカードはカードの一覧から来ること、回復のカードがなければライフは増えないこと（★の型 F、`gameClaims_valid`）
- `CardGen/Turn.lean`：ターンのある対戦（マナとタップ、インスタントとスタック、まとめての攻撃とブロック、デッキ切れ、優先権）
- `CardGen/Warnings.lean`：形式の警告の裏付け（例：種類が空の範囲はどのカードにも当たらない、0のダメージは盤面を変えない）
- `CardGen/TurnProps.lean`：その定理。盤面はターンのないモデルで到達できること（★の引き継ぎ）と、召喚の上限・攻撃の回数・種類ごとの上限・マナの収支など
- `CardGen/Explore.lean`：循環があるときの総当たりの検査
- `CardGen/Timed.lean`：OCG の適用の時刻つきの判定と、証明書つきの総当たり（メタ定理2、`TSys.allEnd_of_certOK`）。テストプレイの無効の判定もこの手順
- `CardGen/Custom.lean`：ユーザーが追加する命題（フィールド上・手札・墓地・デッキの枚数）と反例探し
- `CardGen/Cli.lean`：検査ツール
- `CardGen/Sample.lean`・`CardGen/Mtg.lean`：見本（遊戯王風と MTG 風）と `#guard` のテスト
- `CardGen/Vectors.lean`：C# との差分テスト用のテストベクトル

`csharp/`：Unity で使う C# 実装と差分テスト。`unity/CardGenEditor/`：エディタ（実行時のアプリ）

```
lake build
lake exe cardgen CardGen/sample.json --text
lake exe cardgen CardGen/mtg.json --text
lake exe cardgen --game-vectors CardGen/mtg.json  # そのゲームのテストベクトル（C# との照合用。エディタの「C# と照合」）
python3 jobs/accept.py --recheck                 # 受け入れ済みの証明のジョブを検査し直す
cd csharp/CardGen.Tests && dotnet test           # C# の差分テスト
tools/unity-build.sh                             # Unity のエディタをビルド（Windows 側で）
tools/unity-build.sh --test                      # Unity の画面の自動テスト
tools/unity-build.sh --rclick                    # ビルドしたアプリで、右クリックのメニューが出るかを確かめる
```

WSL では .NET 9 の SDK を `~/.dotnet` に入れて使う（`dotnet-install.sh --channel 9.0 --install-dir ~/.dotnet`、
`export DOTNET_ROOT=~/.dotnet PATH=~/.dotnet:$PATH`）。ドキュメントのサイトは `pip install mkdocs-material==9.5.39`（GitHub Actions と同じ版）。

中間表現は版 11（`CardGen/中間表現.md`）。

`sorry` はなく、証明が使う公理は Lean 標準のもの（`propext`・`Classical.choice`・`Quot.sound`）だけ。
