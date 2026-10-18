# 証明のジョブキュー（手動方式）

自動では証明できない命題を「ジョブ」としてためておき、証明する側（開発中とプロトタイプの間は Claude）が
`sorry` を埋め、`accept.py` が機械的に検査して受け入れる。証明する側が誰でも、受け入れの検査は同じ。

```
jobs/
  claims/      追加したい命題の例（入力）
  pending/     証明待ちのジョブ（0001, 0002, …）
  done/        受け入れたジョブ（Job.lean が検査に通った完全なファイル）
  accept.py    受け入れの検査
```

## 1. 命題を追加して、ジョブを作る

命題は今のところ「（フィールド上・手札・墓地・デッキ）の、条件に合うカードは最大 n 枚」の形
（`CardGen/Custom.lean` の `CustomClaim`）。`place` は `field`・`hand`・`grave`・`deck` のどれかで、省くと `field`。

```json
{"title": "フィールド全体に闇属性の罠は存在しない", "types": ["罠"], "tags": ["闇属性"], "both": true, "n": 0}
{"title": "デッキの魔法は各プレイヤー最大35枚", "types": ["魔法"], "tags": [], "both": false, "n": 35, "place": "deck"}
```

```
lake exe cardgen --job ゲーム.json 命題.json
```

- まず反例を探す。カードの一覧から作ったいくつかのデッキ（条件に合うカードだけ、合うカードとほかの1種類を交互）で、
  条件に合うカードをできるだけ命題の場所に集める対戦（2手先まで見て枚数が増える動きを選ぶ）を、証明済みの
  `State.step?` で実際に進める。命題を破れば、その動きの列を反例として返す（終了コード 1、ジョブは作らない）
- 反例がなければ `jobs/pending/<番号>/` を作る
  - `job.json`：命題・ゲーム・**変えてはいけない頭の部分**（ルールとカードと `JobStatement` の定義）
  - `Proof.lean`：証明を書くファイル。最初は `theorem job_proof : JobStatement := by sorry`

Unity のエディタからは、右下の「命題とジョブ」の欄で同じことができる（検査ツールの `--job-stdin` を WSL 経由で呼ぶ）。
「ジョブの状態を更新」で一覧（`--jobs`）を表示する。

## 2. 証明する（Claude への頼み方）

この会話で「キューを処理して」と頼む。Claude は次の手順で進める。

1. `jobs/pending/` のジョブを番号順に見る
2. `job.json` の `title` と `header` を読み、`Proof.lean` に証明を書く（補題を足してよい。`import`・`axiom`・`sorry`・
   `native_decide`・カーネルの検査を変える設定は使わない）
3. `python3 jobs/accept.py jobs/pending/<番号>` で検査する。通らなければ `result.json` の理由を見て直す
4. 受け入れられたらコミットする。どうしても証明できない命題は、理由（偽だと思う・道具が足りない など）を報告する

## 3. 受け入れの検査（accept.py）

1. `Proof.lean` に検査をすり抜ける書き方がないか調べる（`sorry`・`admit`・`axiom`・`unsafe`・実装の差し替え・
   `native_decide`・`set_option debug…`・`import`・`#exit`）
2. 頭の部分 ＋ `Proof.lean` ＋ 確認の部分をつなげてコンパイルする。確認の部分は
   `example : JobStatement := job_proof`（証明したのが命題そのものか）と `#print axioms job_proof`
3. 公理が `propext`・`Classical.choice`・`Quot.sound` だけなら受け入れて `jobs/done/` へ移す

将来ローカルのモデルに替えるときは、2 の「証明する」部分だけを差し替える。

## これまでのジョブ

| 番号 | 命題 | 結果 |
|---|---|---|
| 0001 | 自分のフィールド上の闇属性のモンスターは最大5枚 | 受け入れ（自動の★「モンスターは最大5枚」から） |
| 0002 | フィールド全体に闇属性の罠は存在しない | 受け入れ（盤面のカードはどれもカードの一覧から来る、という不変条件を証明） |
| 0003 | デッキの魔法は各プレイヤー最大35枚 | 受け入れ（自動の★「デッキは増えない」から） |

反例の例：`jobs/claims/monster-max3.json`（自分のフィールド上のモンスターは最大3枚）は、モンスターを5枚置く対戦が見つかり、ジョブにならない。
`jobs/claims/hand-spell-max2.json`（手札の魔法は最大2枚）も、魔法だけのデッキで引くだけで反例になる。
