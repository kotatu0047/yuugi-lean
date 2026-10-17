# CardGen Editor（Unity・実行時のアプリ）

ノードをつないでカードゲームのルールとカードを作り、その場で形式を検査し、Lean の検査ツールで★と無効の関係を検査するエディタ。

## 開き方

Unity は WSL のファイルシステム上のプロジェクトを開けない（大文字小文字を区別するため）。
Windows 側のクローン（例：`C:\Users\yamam\repo\yuugi-lean`）の `unity/CardGenEditor` を Unity Hub で開く（Unity 6000.6.6f1）。

- メニュー「CardGen ＞ プロジェクトを準備」：PanelSettings とシーン（`Assets/CardGenEditor/Main.unity`）を作る
- メニュー「CardGen ＞ Windows 用にビルド」：`Build/CardGenEditor.exe` を作る

C# の中核（中間表現・形式の検査・盤面の計算）は `csharp/CardGen.Core` をローカルのパッケージとして使う。

## 使い方

| 操作 | やり方 |
|---|---|
| 移動・拡大縮小 | 背景をドラッグ・ホイール |
| ノードを動かす・選ぶ | ノードをドラッグ・クリック |
| つなぐ | 右の丸から別のノードの左の丸へドラッグ（ルール→ゾーン、カード→効果、効果→範囲） |
| つなぎを外す | 左の丸をクリック |
| 追加 | 上の「追加」。ノードを選んだまま追加すると、そのノードからつないだ状態で追加する |
| 開く・保存 | パスを入れて「開く」「保存」（中間表現の JSON） |
| 検査 | 形式の検査は編集のたびに自動。★と無効の関係は「Lean で検査」 |

「Lean で検査」は、右の欄のコマンドで検査ツールを動かす。既定は WSL の中のビルド済みの検査ツール：

```
wsl.exe -e /home/yamam/repo/yuugi-lean/.lake/build/bin/cardgen -
```

（WSL 側で `lake build` しておく。別の場所に置いたときは欄を書き換える）

## 動作確認用のコマンドライン

```
CardGenEditor.exe -cardgen-select 6 -cardgen-check -cardgen-results-end -cardgen-screenshot C:\path\shot.png
```

見本を読み込み、6番のノードを選び、Lean で検査し、結果を一番下まで送って、画面を保存して終了する。
