# yuugi-lean

遊戯王 OCG のルールの Lean 4 による形式化と、それを土台にした「検証付きカードゲームジェネレーター」の検査部分。

## YuugiLean：遊戯王 OCG のルールの形式化

- `YuugiLean/YuGiOh.lean`：ルール・チェーン・永続効果の判定・カードの効果
- `YuugiLean/Invariants.lean` ほか：カードの総数・uid・ゾーンの上限・ターンプレイヤーなどの不変条件の証明
- `YuugiLean/Quad.lean`：スキルドレイン・王宮のお触れ・人造人間－サイコ・ショッカー・D－HERO Bloo－D の「4すくみ」の解析（考察は `4すくみ考察.md`）

## CardGen：検証付きカードゲームジェネレーターの検査

ユーザーがビジュアルエディタで作ったルールとカード（中間表現の JSON）を検査する。企画は `企画書.md`。

- `CardGen/IR.lean`：中間表現（説明は `CardGen/中間表現.md`、見本は `CardGen/sample.json`）
- `CardGen/Model.lean`・`CardGen/Inv.lean`：対戦のモデルと、どの盤面でも成り立つ盤面の制約
- `CardGen/Claims.lean`：ルールから導く性質（★）と、それがすべての対戦で成り立つことの証明（`derived_valid`）
- `CardGen/Negation.lean`：無効の関係に循環がなければ判定が必ず止まり結果が1通りであることの証明（`negation_settles`）
- `CardGen/Explore.lean`：循環があるときの総当たりの検査
- `CardGen/Cli.lean`：検査ツール

```
lake build
lake exe cardgen CardGen/sample.json --text
```

`sorry` はなく、証明が使う公理は Lean 標準のもの（`propext`・`Classical.choice`・`Quot.sound`）だけ。
