# CardGen の C# 実装

Unity で使う、中間表現の読み書き・形式の検査・盤面の計算（`CardGen.Core`、.NET Standard 2.1・C# 9）。
Lean の定義（`CardGen/`）と同じ結果になることを、Lean が書き出したテストベクトル `vectors.json` で確かめる（`CardGen.Tests`）。

```
lake exe cardgen --vectors csharp/vectors.json   # Lean の定義を変えたら書き出し直す（lake build が古さを検出する）
cd csharp/CardGen.Tests && dotnet test
```

| C# | Lean |
|---|---|
| `IrJson.ParseGame` / `IrJson.ToJson` | `fromJson?` / `toJson`（`CardGen/IR.lean`） |
| `Selector.Matches` | `Selector.matches` |
| `Rules.CellOf`・`Cell.Adjacent`・`Slot.ViewFor`（マスの位置と、隣・同じ縦列） | `Rules.cellOf`・`Cell.adjacent`・`Slot.view` |
| `MatchState.FreeCell` | `State.freeCell` |
| `Check.Game` | `Game.check`（誤りの文章も同じ） |
| `PState.Destroy` | `PState.destroy`（`CardGen/Model.lean`） |
| `Negation.InstRel` | `instRel`（`CardGen/Negation.lean`） |
| `Negation.AnalyzeBoard` | `analyzeBoard`（`CardGen/Explore.lean`） |
| `TSys.Succ`（適用の時刻つきの判定の1歩） | `TSys.succ`（`CardGen/Timed.lean`） |
| `MatchState.AtkOf` / `MatchState.DefOf` | `State.atkOf` / `State.defOf`（`CardGen/Model.lean`） |
| `MatchState.Combat`（MTG 式の戦闘。ダメージの割り振りと、守備力以上のダメージを受けたカードの破壊） | `State.combat`・`State.sweep` |
| `Match.Start` / `Match.Step`（ターンのある対戦） | `Match.start` / `Match.step?`（`CardGen/Turn.lean`） |
| `IrJson.Upgrade`（版 2〜7 のファイルを版 8 に上げる） | エディタ用（Lean は今の版だけを読む） |
| `MatchState.Start` / `MatchState.Step` | `start` / `State.step?`（`CardGen/Play.lean`。`step?_sound` で証明に使う動きの関係と結びついている） |
| `Judge`（対戦中の無効の判定。カードごとの有効・無効と適用の順番を覚え、盤面が変わるたびに `TSys.Succ` で進める） | テストプレイ用。`JudgeTests` で Bloo－D・スキルドレイン・お触れの場面を確かめる |
| `GraphDoc`（ノードのグラフ。`RenameValue` で集合の値の名前を、使っているところもまとめて変える）・`Report`（検査ツールの報告） | エディタ用（Lean 側に対応なし） |
| `Slot.Key`（ダメージが変わっても同じカードを見分ける鍵） | エディタ用（`Judge` が使う。Lean のモデルはカードを位置で指す） |
