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
| `Check.Game` | `Game.check`（誤りの文章も同じ） |
| `PState.Destroy` | `PState.destroy`（`CardGen/Model.lean`） |
| `Negation.InstRel` | `instRel`（`CardGen/Negation.lean`） |
| `Negation.AnalyzeBoard` | `analyzeBoard`（`CardGen/Explore.lean`） |
| `MatchState.Start` / `MatchState.Step` | `start` / `State.step?`（`CardGen/Play.lean`。`step?_sound` で証明に使う動きの関係と結びついている） |
| `GraphDoc`（ノードのグラフ）・`Report`（検査ツールの報告） | エディタ用（Lean 側に対応なし） |
