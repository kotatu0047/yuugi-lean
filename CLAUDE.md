# CLAUDE.md

このリポジトリで作業するエージェントへの決まり。ここに書くのは「お願い」で、守らせる仕組みは別にある
（`spec/check.sh`・CI・`.claude/settings.json` の書き込み禁止とフック）。

## 返答と進め方

- 報告・質問は日本語で書く（長い作業や会話の要約の後でも）。コミットメッセージも日本語。
- 聞かないと分からないことが出てくるまで、できるだけ自分で進める。

## コミットと push

- 作業（ファイルの変更）が一段落したら、確認なしでコミットし、`git push` まで行う（master に直接）。
- コミットの前に `tools/check-all.sh` が走る（コミット前のフック `.githooks/pre-commit`。
  有効にするのは `git config core.hooksPath .githooks`）。証明のゲート・C# のテスト・ドキュメントのサイト・
  Unity の画面のテストとビルドをすべて行う。Unity に関係しない変更なら `CARDGEN_NO_UNITY=1 git commit …` で
  Unity を飛ばしてよい。失敗したら直してからコミットする（`--no-verify` で飛ばさない）。
- push が権限で止められたら、回避せずにユーザーに `! git push` を頼む。
- リポジトリは公開。秘密の情報（トークン・パスワード・個人のメールアドレスなど）をファイルにもコミットにも入れない。

## 決まった頼み方

- 「会話ログをコミットしてプッシュして」：`.claude-history/` だけをコミット（メッセージは「会話記録を更新する」）して push する。
  会話記録は Stop フック（`.claude/hooks/save-history.py`）が書き直すので、自分では編集しない。
- 「キューを処理して」：`jobs/README.md` の手順で、証明のジョブを番号順に処理する（下の「ルールの前提」）。

## WSL の道具

- 必要なソフトは、自分の判断で WSL に入れてよい（sudo なしでホームの下に入れるのを優先）。
- .NET 9 SDK は `~/.dotnet`：`DOTNET_ROOT=~/.dotnet ~/.dotnet/dotnet test`（`csharp/CardGen.Tests` で）。
- ドキュメントのサイトは mkdocs-material 9.5.39（CI と同じ版）。
- Unity のエディタは Windows 側でビルドする：`tools/unity-build.sh`。画面の撮影は `tools/unity-build.sh --shot <png> [引数]`。
  前のプロセスが残っていたら `taskkill.exe /IM CardGenEditor.exe /F` で止めてからやり直す。

## 「証明済み」の定義

- **`spec/check.sh` が通ること**だけを「証明済み」「解決した」とする。作業を終える前に走らせる（Stop フックでも
  `spec/check.sh --quick` が走り、通らなければ差し戻される）。
- ビルドが通った補題の本数は進捗ではない。主張が `spec/Spec/Statements.lean` と一致しない定理や、
  そこから使われない補題がいくつ通っても、それだけでは何も示していない。
- ゲートに通らないまま終えるときは、「証明済み」とは報告せず、通らない理由と、どこまでできたかをそのまま報告する。

## 証明の書き方

- 使ってよい公理は `propext`・`Classical.choice`・`Quot.sound` だけ。
- `sorry`・`admit`・`axiom`・`native_decide`（`decide +native`）・`unsafe`・`implemented_by`・`@[extern]`・
  `debug.skipKernelTC`・`#exit` は使わない（`spec/scan.py` が CardGen のソースを調べる）。
- 証明が詰まったとき、命題を弱める・仮定を足す・自明な形に書き換えることで「通す」のは禁止。
  必要なら、命題を変える案とその理由をユーザーに示して判断を頼む。

## 守るファイル（変えない）

次のファイルは変更しない。変更が必要なら、差分の案と理由を返答に書いてユーザーに頼む
（ユーザーが自分で直すか、`! git apply` で当てる）。

- `spec/`：凍結した主張（`Spec/Statements.lean`）と、その検査（`Spec/Check.lean`・`check.sh` ほか）
- `.claude/settings.json`・`.claude/hooks/`・`.github/workflows/`・`.githooks/`・`tools/check-all.sh`・
  `jobs/accept.py`・`lakefile.toml`・`lean-toolchain`

### 新しい定理を「証明済み」としてレポートに出すとき

`CardGen/Report.lean` が名前を出す定理は、どれも `spec/` で主張と照合されていなければならない
（`spec/report_names.py` が確かめる）。新しい定理を出すときは、`Spec/Statements.lean` に足す主張と
`Spec/Check.lean` に足す2行（`theorem … := @CardGen.…` と `#assert_std_axioms …`）を案として示す。

### 主張に出てくる定義を変えるとき

凍結した主張は `CardGen` の定義（`Reachable`・`Step`・`Match.step?`・`Claim.Valid` など）を使っている。
定義を変えると、主張の文面は同じでも意味が変わる。`CardGen/Model.lean`・`Turn.lean`・`Claims.lean` などで
これらの定義を変えたときは、何をどう変えたかを返答とコミットメッセージに明記する。

## ルールの前提

- 盤面のグリッドは 49×49 のまま。エクストラモンスターゾーンは入れない。
- `YuugiLean/` は最初の検証実験用で、今後は使わない（`lake build` の既定にも含めない）。
- 証明のジョブキューの手順は `jobs/README.md`。開発中は Claude が証明する側を代行する
  （`python3 jobs/accept.py jobs/pending/<番号>` が通るまで直す。証明できないものは理由を報告する）。

## よく使うコマンド

```
spec/check.sh                 # 証明のゲート（全部）
spec/check.sh --quick         # leanchecker とジョブの再検査を飛ばす
lake build                    # CardGen・検査ツール・Spec
tools/check-all.sh --no-unity # コミット前と同じ検査（C#・ドキュメントも）
```
