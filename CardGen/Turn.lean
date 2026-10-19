import CardGen.Play
import CardGen.Pool

/-!
# ターン

`Step`（`Model.lean`）は、どちらのプレイヤーもいつでも何度でも動ける、実際の対戦より自由なモデルである。
ここではその上に**ターン**を重ねる。状態は盤面（`State`）とターンの情報（`TurnInfo`）の組（`Match`）で、
実行できる1歩 `Match.step?` で進める。

- カードを置く・攻撃するのはターンプレイヤーだけ。場のカードの発動はどちらのプレイヤーもいつでもできる
- 戦闘できる種類のカードを置くのは、1ターンに `Rules.summonsPerTurn` 枚まで（通常召喚。0 なら制限なし）
- 戦闘できるカードの攻撃は、1ターンに1枚1回まで。先攻の最初のターンは `Rules.firstTurnAttack` のときだけ攻撃できる
- 「ターン終了」で相手のターンになり、新しいターンプレイヤーが `Rules.drawPerTurn` 枚引く
  （デッキが足りなければある分だけ）。先攻の最初のターンは `Rules.firstTurnDraw` のときだけ引く
- 自由に引く動きはない（引くのはターンの最初と、効果によるときだけ）
- マナ：ターンプレイヤーは、表側表示の「フィールド上」の、マナを出すカード（`Card.mana`）をタップして、
  その色（`Card.manaColor`。`""` は無色）のマナを得る。カードを置くには、どのマナで払うか（`pay`）を選ぶ。
  払うマナは持っているマナの一部で、色の決まったコスト（`Card.colorCost`）を含み、全部でコストの合計
  （`Card.cost` ＋ 色の決まったコストの数）だけ。マナはターンの終わりに消える
- タップしたカードは、持ち主の次のターンの始めに起きる（アンタップ）。`Rules.attackTaps` なら攻撃でもタップし、
  タップしているカードは攻撃できない
- 種類ごとに、1ターンに置ける枚数の上限（`Rules.placeLimits`。例：土地は1ターンに1枚）
- `Rules.summoningSickness` なら、置いたターンの戦闘できるカードは攻撃もタップもできない（召喚酔い）
- MTG 式の戦闘（`Rules.blocking`）では、ターンプレイヤーは攻撃するカードを1枚ずつ宣言し（何枚でもよい）、
  攻撃されたプレイヤーがまとめてブロックを選ぶ（1枚の攻撃を何枚でブロックしてもよい）。そこで戦闘のダメージを与える
- インスタント（`Rules.instants` の種類）は、いつでも置ける。ターンプレイヤーでない方も、相手のターンにタップして
  出したマナで置ける（`cast`）。それ以外のカードは、攻撃の途中やスタックが空でないときには置けない
- スタック（`Rules.stack`）：「フィールド上」でないゾーンに置いた、発動する効果を持つカード（呪文）は、スタックに積まれ、
  一番上のものしか解決できない。スタックが空になるまで、攻撃・ブロック・ターン終了はできない
- 飛行を持つカードの攻撃は、飛行か到達を持つカードでしかブロックできない
- 状態の確認（`settle`）：どちらのプレイヤーもいつでも、守備力以上のダメージを受けている（MTG 式の戦闘では守備力が 0 の）
  戦闘できるカードを破壊させられる（テストプレイは動きのたびに自動で行う）
- ターンの終わりに、どのカードのダメージとターンの終わりまでの変化も消える。ターンの最初に引く枚数が足りなければ、そのプレイヤーの負け
- ライフのルールがあって、どちらかのライフが 0 になったときと、デッキ切れのときは、対戦が終わる（それ以上動けない）

**ターンのある対戦の盤面は、どれもターンのないモデルで到達できる盤面**（`TReachable.reachable`）。
1歩はどれも `Step` の0回以上の繰り返しになるからである。そのため、盤面の制約（`Reachable.inv`）、
★（`derived_valid`・`gameClaims_valid`）、受け入れた証明のジョブは、ターンのある対戦でもそのまま成り立つ
（`TReachable.of_reachable`）。そのうえで、ターンがあるから言える性質（`TReachable.summons_le` など）を示す。
-/

namespace CardGen

/-- カードの記録を、今のフィールドにあるものだけに絞る。同じカードが複数あれば、フィールドにある枚数まで残す -/
def prune : List Slot → List Slot → List Slot
  | [], _ => []
  | a :: as, f => if a ∈ f then a :: prune as (f.erase a) else prune as f

/-- `l` の各カードの枚数が、`f` の枚数以下（`l` は `f` の一部を取り出したもの） -/
def BagLe (l f : List Slot) : Prop := ∀ a, l.count a ≤ f.count a

theorem prune_bagLe : ∀ (as f : List Slot), BagLe (prune as f) f
  | [], f => by intro a; simp [prune]
  | x :: as, f => by
    intro a
    unfold prune
    split
    · rename_i hx
      have ih := prune_bagLe as (f.erase x) a
      rw [List.count_erase] at ih
      rw [List.count_cons]
      by_cases hxa : x = a
      · subst hxa
        have := List.count_pos_iff.2 hx
        simp at ih ⊢
        omega
      · have : (x == a) = false := by simpa using hxa
        simp [this] at ih ⊢
        omega
    · exact prune_bagLe as f a

/-- ターンの情報。カードの記録はダメージを除いたもの（`Slot.base`）で覚える -/
structure TurnInfo where
  /-- ターンプレイヤー -/
  tp : PlayerId
  /-- 何ターン目か（1 から） -/
  count : Nat := 1
  /-- このターンに置いた、戦闘できる種類のカードの枚数 -/
  summons : Nat := 0
  /-- このターンに攻撃したカード（ターンプレイヤーのフィールドにあるものだけ） -/
  attacked : List Slot := []
  /-- このターンにターンプレイヤーが置いたカードの種類（置いた順） -/
  placed : List TypeName := []
  /-- このターンに置いたカード（ターンプレイヤーのフィールドにあるものだけ。召喚酔いに使う） -/
  entered : List Slot := []
  /-- ターンプレイヤーのマナ（色の名前を、1マナにつき1つ並べたもの。`""` は無色）。タップで増え、カードを置くと減る。
  ターンの終わりに消える -/
  pool : List String := []
  /-- 相手のマナ（インスタントを置くために、このターンにタップして出したもの） -/
  oppPool : List String := []
  /-- タップしている、ターンプレイヤーのカード -/
  tapped : List Slot := []
  /-- タップしている、相手のカード（相手の次のターンの始めに起きる） -/
  oppTapped : List Slot := []
  /-- 攻撃を宣言して、ブロックを待っているカード（宣言した順）。MTG 式の戦闘だけで使う -/
  attackers : List Slot := []
  /-- このターンにブロックした、相手のカード（相手のフィールドにあるものだけ） -/
  blocked : List Slot := []
  /-- スタック（一番上から順に、置いたプレイヤーとカード） -/
  stack : List (PlayerId × Slot) := []
  /-- このターンにタップで出したマナの合計（両方のプレイヤー） -/
  made : Nat := 0
  /-- このターンに払ったマナの合計（両方のプレイヤー） -/
  spent : Nat := 0
  /-- ターンの最初に引く枚数が足りずに負けたプレイヤー -/
  decked : Option PlayerId := none
  /-- 優先権を持つプレイヤー（公理：優先権を持つプレイヤーだけが動ける） -/
  prio : PlayerId := tp
  /-- 続けてパスした回数（2 なら両者がパスした：スタックの一番上の解決か、ブロックを待つ） -/
  passes : Nat := 0
deriving Repr, DecidableEq

/-- ターンのある対戦の状態 -/
structure Match where
  g : State
  turn : TurnInfo

/-- ターンのある対戦の動き -/
inductive TChoice
  /-- ターンプレイヤーが手札の `hand` 番目のカードを `zone` 番目のゾーンの `cell` 番目のマスに置く。`pay`：払うマナ -/
  | place (hand : Nat) (zone : Nat) (cell : Nat) (up : Bool) (pay : List String := [])
  /-- ターンプレイヤーでない方が、手札の `hand` 番目のインスタントを置く。`pay`：払うマナ -/
  | cast (hand : Nat) (zone : Nat) (cell : Nat) (up : Bool) (pay : List String := [])
  /-- `p` がフィールドの `k` 番目のカードの `eff` 番目の効果を発動して解決する（どちらのターンでもよい） -/
  | resolve (p : PlayerId) (k : Nat) (eff : Nat) (apply : Bool) (neg : List Pos := []) (tgt : Option Pos := none)
  /-- ターンプレイヤーがフィールドの `k` 番目のカードで攻撃する（MTG 式の戦闘では攻撃の宣言だけで、`target` は `none`） -/
  | attack (k : Nat) (target : Option Nat) (neg : List Pos)
  /-- MTG 式の戦闘で、攻撃されたプレイヤーがブロックを選ぶ：`(j, a)` はフィールドの `j` 番目のカードで、
  `a` 番目に宣言された攻撃をブロックする（空ならブロックしない）。そこで戦闘のダメージを与える -/
  | block (blocks : List (Nat × Nat)) (neg : List Pos)
  /-- ターンプレイヤーがフィールドの `k` 番目のカードをタップしてマナを出す（`color`：2色以上から選べるときの色） -/
  | tap (k : Nat) (color : String := "")
  /-- ターンプレイヤーでない方が、フィールドの `k` 番目のカードをタップしてマナを出す -/
  | oppTap (k : Nat) (color : String := "")
  /-- ターンを終え、相手のターンにする -/
  | endTurn
  /-- 状態の確認（どちらのプレイヤーでも、いつでも。優先権は変わらない） -/
  | settle (neg : List Pos)
  /-- 優先権を持つプレイヤーがパスする（優先権が相手に移る） -/
  | pass
deriving Repr, DecidableEq

/-- `n` 枚引く（デッキが足りなければある分だけ） -/
def State.drawUpTo (r : Rules) (p : PlayerId) : Nat → State → State
  | 0, g => g
  | n + 1, g =>
    match g.step? r (.draw p) with
    | some g' => State.drawUpTo r p n g'
    | none => g

/-- 開始時の状態（`first` が先攻）。先攻の最初のターンに引くルールなら引く -/
def Match.start (r : Rules) (decks : PlayerId → List Card) (first : PlayerId) : Match :=
  ⟨if r.firstTurnDraw then (CardGen.start r decks).drawUpTo r first r.drawPerTurn else CardGen.start r decks,
   { tp := first }⟩

/-- フィールドのカードの、ダメージを除いたもの -/
def PState.bases (s : PState) : List Slot := s.field.map Slot.base

/-- スタックの記録を、今のフィールドにあるものだけに絞る（同じカードが複数あれば、フィールドにある枚数まで残す） -/
def pruneStack : List (PlayerId × Slot) → (PlayerId → List Slot) → List (PlayerId × Slot)
  | [], _ => []
  | (q, a) :: as, f =>
    if a ∈ f q then (q, a) :: pruneStack as (fun x => if x = q then (f q).erase a else f x) else pruneStack as f

/-- カードの記録を、新しい盤面に合わせる（ターンプレイヤーと相手のフィールドにあるものだけにする） -/
def TurnInfo.prune (t : TurnInfo) (g : State) : TurnInfo :=
  { t with attacked := CardGen.prune t.attacked (g t.tp).bases,
           entered := CardGen.prune t.entered (g t.tp).bases,
           tapped := CardGen.prune t.tapped (g t.tp).bases,
           oppTapped := CardGen.prune t.oppTapped (g (!t.tp)).bases,
           attackers := CardGen.prune t.attackers (g t.tp).bases,
           blocked := CardGen.prune t.blocked (g (!t.tp)).bases,
           stack := pruneStack t.stack fun q => (g q).bases }

/-- 記録 `l` にない（同じカードのうち、記録にない1枚がフィールドにある） -/
def notIn (l field : List Slot) (sl : Slot) : Bool := decide (l.count sl.base < (field.map Slot.base).count sl.base)

/-- `l` の各要素の個数が、`m` の個数以下（多重集合として含まれる） -/
def bagLeB (l m : List String) : Bool := l.all fun a => decide (l.count a ≤ m.count a)

/-- マナ `pay` でカード `c` のコストを払えるか：持っているマナ `pool` の一部で、色の決まったコストを含み、全部でコストの合計 -/
def payOK (c : Card) (pool pay : List String) : Bool :=
  bagLeB pay pool && bagLeB c.colorCost pay && pay.length == c.cost + c.colorCost.length

/-- 払い方を1つ選ぶ（テストプレイの既定の払い方）：色の決まったコストはその色で払い、残りは無色のマナから先に、
次に持っている順に払う。払えなければ `none`。どの払い方も `payOK` を満たす（`autoPay_ok`） -/
def autoPay (c : Card) (pool : List String) : Option (List String) :=
  let rest := c.colorCost.foldl List.erase pool
  let generic := rest.filter (· == "") ++ rest.filter (· != "")
  let pay := c.colorCost ++ generic.take c.cost
  if payOK c pool pay then some pay else none

theorem autoPay_ok {c : Card} {pool pay : List String} (h : autoPay c pool = some pay) : payOK c pool pay = true := by
  simp only [autoPay] at h
  split at h
  · cases h; assumption
  · cases h

/-- 攻撃の途中でも、スタックが空でなくてもないか -/
def TurnInfo.quiet (t : TurnInfo) : Bool := t.attackers.isEmpty && t.stack.isEmpty

/-- いつでも置ける種類（インスタント）のカードか -/
def Rules.instant (r : Rules) (c : Card) : Bool := r.instants.contains c.type

/-- 置くとスタックに積まれるか（スタックのルールで、「フィールド上」でないゾーンに置く、発動する効果を持つカード） -/
def Rules.spell (r : Rules) (sl : Slot) : Bool :=
  r.stack && !r.onFieldZone sl.zone && sl.card.effects.any fun | .activated _ => true | _ => false

/-- スタックに積む -/
def TurnInfo.push (r : Rules) (t : TurnInfo) (p : PlayerId) (sl : Slot) : List (PlayerId × Slot) :=
  if r.spell sl then (p, sl.base) :: t.stack else t.stack

/-- このターンに、ターンプレイヤーがカード `sl` を、マナ `pay` で払って置けるか
（置ける時か・召喚の上限・種類ごとの上限・マナ） -/
def TurnInfo.placeOK (r : Rules) (t : TurnInfo) (sl : Slot) (pay : List String) : Bool :=
  (t.quiet || r.instant sl.card) &&
  (!r.fights sl || r.summonsPerTurn == 0 || decide (t.summons < r.summonsPerTurn)) &&
  r.placeLimits.all (fun l => !l.types.contains sl.card.type ||
    decide ((t.placed.filter l.types.contains).length < l.count)) &&
  payOK sl.card t.pool pay

/-- カード `sl` を、マナ `pay` で払って置いたあとのターンの情報 -/
def TurnInfo.afterPlace (r : Rules) (t : TurnInfo) (sl : Slot) (pay : List String) : TurnInfo :=
  { t with summons := t.summons + (if r.fights sl then 1 else 0), placed := t.placed ++ [sl.card.type],
           entered := sl.base :: t.entered, pool := pay.foldl List.erase t.pool, spent := t.spent + pay.length,
           stack := t.push r t.tp sl }

/-- ターンプレイヤーでない方が、インスタント `sl` をマナ `pay` で払って置けるか -/
def TurnInfo.castOK (r : Rules) (t : TurnInfo) (sl : Slot) (pay : List String) : Bool :=
  r.instant sl.card && payOK sl.card t.oppPool pay

/-- ターンプレイヤーでない方がインスタントを置いたあとのターンの情報 -/
def TurnInfo.afterCast (r : Rules) (t : TurnInfo) (sl : Slot) (pay : List String) : TurnInfo :=
  { t with oppPool := pay.foldl List.erase t.oppPool, spent := t.spent + pay.length, stack := t.push r (!t.tp) sl }

/-- 召喚酔いで動けないか（置いたターンの、戦闘できるカード） -/
def TurnInfo.sick (r : Rules) (t : TurnInfo) (field : List Slot) (sl : Slot) : Bool :=
  r.summoningSickness && r.fights sl && !notIn t.entered field sl

/-- フィールドのカード `sl` で、このターンに攻撃できるか（スタックが空のときだけ） -/
def TurnInfo.attackOK (r : Rules) (t : TurnInfo) (field : List Slot) (sl : Slot) : Bool :=
  t.stack.isEmpty && (r.firstTurnAttack || t.count != 1) && notIn t.attacked field sl &&
  (!r.attackTaps || notIn t.tapped field sl) && !t.sick r field sl

/-- タップして出るマナ（`color`：2色以上から選べるときの色。選べない色なら `none`） -/
def manaOut (c : Card) (color : String) : Option (List String) :=
  if c.manaChoice.isEmpty then some (List.replicate c.mana c.manaColor)
  else if c.manaChoice.contains color then some (List.replicate c.mana color) else none

/-- ターンプレイヤーが、フィールドのカード `sl` をタップしてマナを出せるか -/
def TurnInfo.tapOK (r : Rules) (t : TurnInfo) (field : List Slot) (sl : Slot) : Bool :=
  sl.faceUp && r.onFieldZone sl.zone && decide (0 < sl.card.mana) && notIn t.tapped field sl && !t.sick r field sl

/-- ターンプレイヤーでない方が、フィールドのカード `sl` をタップしてマナを出せるか -/
def TurnInfo.oppTapOK (r : Rules) (t : TurnInfo) (field : List Slot) (sl : Slot) : Bool :=
  sl.faceUp && r.onFieldZone sl.zone && decide (0 < sl.card.mana) && notIn t.oppTapped field sl

/-- カード `sl` で攻撃したあとのターンの情報 -/
def TurnInfo.afterAttack (r : Rules) (t : TurnInfo) (sl : Slot) : TurnInfo :=
  { t with attacked := sl.base :: t.attacked, tapped := if r.attackTaps then sl.base :: t.tapped else t.tapped }

/-- カード `sl` をタップしてマナ `out` を出したあとのターンの情報 -/
def TurnInfo.afterTap (t : TurnInfo) (sl : Slot) (out : List String) : TurnInfo :=
  { t with pool := t.pool ++ out, tapped := sl.base :: t.tapped, made := t.made + out.length }

/-- ターンプレイヤーでない方が、カード `sl` をタップしてマナ `out` を出したあとのターンの情報 -/
def TurnInfo.afterOppTap (t : TurnInfo) (sl : Slot) (out : List String) : TurnInfo :=
  { t with oppPool := t.oppPool ++ out, oppTapped := sl.base :: t.oppTapped, made := t.made + out.length }

/-- ターン終了のあと、相手のターンの情報（相手のタップしていたカードは起き、自分のは残る） -/
def TurnInfo.next (t : TurnInfo) : TurnInfo := { tp := !t.tp, count := t.count + 1, oppTapped := t.tapped }

/-- ブロックに選んだ相手のカード（ダメージを除いたもの） -/
def blockers (opp : List Slot) (blocks : List (Nat × Nat)) : List Slot :=
  blocks.filterMap fun b => opp[b.1]?.map Slot.base

/-- 相手のフィールド `opp` のカードでブロックを選べるか：スタックが空で、攻撃を待っていて、ブロックするカードは
どれも別のカードで、このターンにまだブロックしておらず、攻撃でタップするルールならタップしていない
（同じカードが複数あれば、その枚数まで） -/
def TurnInfo.blockOK (r : Rules) (t : TurnInfo) (opp : List Slot) (blocks : List (Nat × Nat)) : Bool :=
  let bs := blockers opp blocks
  t.stack.isEmpty && !t.attackers.isEmpty && decide (blocks.map (·.1)).Nodup && bs.length == blocks.length &&
  blocks.all (fun b => decide (b.2 < t.attackers.length)) &&
  (bs.all fun b => decide (bs.count b + t.blocked.count b ≤ (opp.map Slot.base).count b) &&
    (!r.attackTaps || decide (bs.count b + t.oppTapped.count b ≤ (opp.map Slot.base).count b))) &&
  blocks.all fun b => match t.attackers[b.2]?, opp[b.1]? with
    | some a, some tl => !a.card.flying || tl.card.flying || tl.card.reach
    | _, _ => false

/-- ブロックのあとのターンの情報 -/
def TurnInfo.afterBlock (t : TurnInfo) (opp : List Slot) (blocks : List (Nat × Nat)) : TurnInfo :=
  { t with attackers := [], blocked := blockers opp blocks ++ t.blocked }

/-- 記録 `rec` のカードの、フィールド `field` での位置（同じカードが複数あれば、まだ選んでいない前のものから） -/
def locate (field : List Slot) : List Slot → List Nat → List Nat
  | [], _ => []
  | a :: as, used =>
    match (List.range field.length).find? (fun i => (field[i]?.map Slot.base) == some a && !used.contains i) with
    | some i => i :: locate field as (used ++ [i])
    | none => locate field as used

/-- スタックの一番上が、`p` のフィールドの `k` 番目のカードか（スタックが空か、スタックのルールがなければ、どれでもよい） -/
def TurnInfo.topOK (r : Rules) (t : TurnInfo) (g : State) (p : PlayerId) (k : Nat) : Bool :=
  !r.stack || match t.stack with
    | [] => true
    | (q, top) :: _ => q == p && ((g p).field[k]?.map Slot.base) == some top

/-- 解決したあとのスタック（一番上を解決したなら取り除く） -/
def TurnInfo.pop (r : Rules) (t : TurnInfo) : TurnInfo :=
  if r.stack then { t with stack := t.stack.drop 1 } else t

/-- 対戦が終わっているか（デッキ切れか、ライフのルールでどちらかのライフが 0） -/
def Match.over (r : Rules) (m : Match) : Bool :=
  m.turn.decked.isSome || (decide (0 < r.life) && ((m.g true).life == 0 || (m.g false).life == 0))

/-- 選んだ動きをしたあとの状態（できない動きなら `none`）。盤面を計算済みの値にする前のもの -/
def Match.step0? (r : Rules) (m : Match) (ch : TChoice) : Option Match :=
  if m.over r then none else
  let tp := m.turn.tp
  match ch with
  | .place h i j up pay =>
    match (m.g tp).hand[h]? with
    | none => none
    | some c =>
      if m.turn.placeOK r ⟨i, j, c, up, 0, 0, 0⟩ pay then
        (m.g.step? r (.place tp h i j up)).map fun g => ⟨g, (m.turn.afterPlace r ⟨i, j, c, up, 0, 0, 0⟩ pay).prune g⟩
      else none
  | .cast h i j up pay =>
    match (m.g (!tp)).hand[h]? with
    | none => none
    | some c =>
      if m.turn.castOK r ⟨i, j, c, up, 0, 0, 0⟩ pay then
        (m.g.step? r (.place (!tp) h i j up)).map fun g => ⟨g, (m.turn.afterCast r ⟨i, j, c, up, 0, 0, 0⟩ pay).prune g⟩
      else none
  | .resolve p k e apply neg tgt =>
    if m.turn.topOK r m.g p k then
      (m.g.step? r (.resolve p k e apply neg tgt)).map fun g => ⟨g, (m.turn.pop r).prune g⟩
    else none
  | .settle neg => some ⟨m.g.sweep r neg, m.turn.prune (m.g.sweep r neg)⟩
  | .pass => none
  | .attack k t neg =>
    match (m.g tp).field[k]? with
    | none => none
    | some sl =>
      if m.turn.attackOK r (m.g tp).field sl then
        if r.blocking then
          -- 攻撃の宣言：相手がブロックを選ぶまで待つ
          if sl.faceUp && r.fights sl && t.isNone then
            some ⟨m.g, { m.turn.afterAttack r sl with attackers := m.turn.attackers ++ [sl.base] }.prune m.g⟩
          else none
        else if m.turn.quiet then
          (m.g.step? r (.attack tp k t neg)).map fun g => ⟨g, (m.turn.afterAttack r sl).prune g⟩
        else none
      else none
  | .block blocks neg =>
    if m.turn.blockOK r (m.g (!tp)).field blocks then
      (m.g.step? r (.combat tp (locate (m.g tp).field m.turn.attackers []) blocks neg)).map fun g =>
        ⟨g, (m.turn.afterBlock (m.g (!tp)).field blocks).prune g⟩
    else none
  | .tap k color =>
    match (m.g tp).field[k]? with
    | none => none
    | some sl =>
      match manaOut sl.card color with
      | none => none
      | some out =>
        if m.turn.tapOK r (m.g tp).field sl then some ⟨m.g, (m.turn.afterTap sl out).prune m.g⟩ else none
  | .oppTap k color =>
    match (m.g (!tp)).field[k]? with
    | none => none
    | some sl =>
      match manaOut sl.card color with
      | none => none
      | some out =>
        if m.turn.oppTapOK r (m.g (!tp)).field sl then some ⟨m.g, (m.turn.afterOppTap sl out).prune m.g⟩ else none
  | .endTurn =>
    if m.turn.quiet then
      let g1 := m.g.mend
      let g := g1.drawUpTo r (!tp) r.drawPerTurn
      some ⟨g, { m.turn.next with
        decked := if (g1 (!tp)).deck.length < r.drawPerTurn then some (!tp) else none }.prune g⟩
    else none

/-! ## 優先権（公理） -/

/-- 優先権とパスの回数だけを変える -/
def TurnInfo.withPrio (t : TurnInfo) (p : PlayerId) (n : Nat) : TurnInfo := { t with prio := p, passes := n }

/-- 動きをするプレイヤー -/
def TChoice.actor (tp : PlayerId) : TChoice → PlayerId
  | .cast .. | .oppTap .. | .block .. => !tp
  | .resolve p .. => p
  | _ => tp

/-- 両者が続けてパスしたあとにだけできる動きか（スタックの一番上の解決と、ブロック） -/
def TurnInfo.afterPasses (r : Rules) (t : TurnInfo) : TChoice → Bool
  | .resolve .. => r.stack && !t.stack.isEmpty
  | .block .. => true
  | _ => false

/-- 優先権について、その動きをしてよいか：両者がパスしたあとの動きは、両者がパスしたときだけ。
それ以外の動きは、優先権を持つプレイヤーが、両者がパスする前に行う。状態の確認はいつでもよい -/
def TurnInfo.prioOK (r : Rules) (t : TurnInfo) (ch : TChoice) : Bool :=
  match ch with
  | .settle _ => true
  | _ => if t.afterPasses r ch then t.passes == 2 else t.passes < 2 && ch.actor t.tp == t.prio

/-- パスしたあとのターンの情報：優先権が相手に移る。両者がパスしても、スタックが空で攻撃の途中でもなければ、
何も起きずにターンプレイヤーに優先権が戻る -/
def TurnInfo.afterPass (t : TurnInfo) : TurnInfo :=
  if t.passes + 1 < 2 then t.withPrio (!t.prio) (t.passes + 1)
  else if t.quiet then t.withPrio t.tp 0
  else t.withPrio (!t.prio) 2

/-- 動いたあとの優先権：動いた本人が持ち続ける。両者がパスしたあとの動き（解決・ブロック）のあとはターンプレイヤーに戻る。
ターン終了のあとは新しいターンプレイヤー。状態の確認では変わらない -/
def TurnInfo.prioAfter (r : Rules) (before after : TurnInfo) (ch : TChoice) : TurnInfo :=
  match ch with
  | .settle _ => after.withPrio before.prio before.passes
  | .endTurn => after.withPrio after.tp 0
  | _ => if before.afterPasses r ch then after.withPrio after.tp 0 else after.withPrio (ch.actor before.tp) 0

/-- 優先権を考えた1歩（盤面を計算済みの値にする前） -/
def Match.step1? (r : Rules) (m : Match) (ch : TChoice) : Option Match :=
  if m.over r then none else
  match ch with
  | .pass => if m.turn.passes < 2 then some ⟨m.g, m.turn.afterPass⟩ else none
  | ch =>
    if m.turn.prioOK r ch then
      (m.step0? r ch).map fun m' => ⟨m'.g, m.turn.prioAfter r m'.turn ch⟩
    else none

/-- 選んだ動きをしたあとの状態（できない動きなら `none`）。盤面は計算済みの値にする（`State.fresh`） -/
def Match.step? (r : Rules) (m : Match) (ch : TChoice) : Option Match :=
  match m.step1? r ch with
  | some m' => some ⟨State.of (m'.g true) (m'.g false), m'.turn⟩
  | none => none

/-- 開始時の状態から、`step?` を繰り返して到達できる -/
inductive TReachable (r : Rules) (decks : PlayerId → List Card) (first : PlayerId) : Match → Prop
  | start : TReachable r decks first (Match.start r decks first)
  | step {m m'} (ch : TChoice) : TReachable r decks first m → m.step? r ch = some m' → TReachable r decks first m'

/-! ## 1歩の中身 -/

/-- 1歩のあとの盤面は、ターンのないモデルで、もとの盤面から到達できる盤面（`Step` の0回以上の繰り返し）。
ターンの情報は、ある記録をその盤面に合わせたもの -/
inductive Match.Moved (r : Rules) (m : Match) : TChoice → Match → Prop
  | place {h i j up pay c g} : (m.g m.turn.tp).hand[h]? = some c → m.turn.placeOK r ⟨i, j, c, up, 0, 0, 0⟩ pay →
      m.g.step? r (.place m.turn.tp h i j up) = some g →
      Match.Moved r m (.place h i j up pay) ⟨g, (m.turn.afterPlace r ⟨i, j, c, up, 0, 0, 0⟩ pay).prune g⟩
  | cast {h i j up pay c g} : (m.g (!m.turn.tp)).hand[h]? = some c → m.turn.castOK r ⟨i, j, c, up, 0, 0, 0⟩ pay →
      m.g.step? r (.place (!m.turn.tp) h i j up) = some g →
      Match.Moved r m (.cast h i j up pay) ⟨g, (m.turn.afterCast r ⟨i, j, c, up, 0, 0, 0⟩ pay).prune g⟩
  | resolve {p k e apply neg tgt g} : m.g.step? r (.resolve p k e apply neg tgt) = some g →
      Match.Moved r m (.resolve p k e apply neg tgt) ⟨g, (m.turn.pop r).prune g⟩
  | settle {neg} : Match.Moved r m (.settle neg) ⟨m.g.sweep r neg, m.turn.prune (m.g.sweep r neg)⟩
  | declare {k t neg sl} : (m.g m.turn.tp).field[k]? = some sl →
      Match.Moved r m (.attack k t neg)
        ⟨m.g, { m.turn.afterAttack r sl with attackers := m.turn.attackers ++ [sl.base] }.prune m.g⟩
  | block {blocks neg g} :
      m.g.step? r (.combat m.turn.tp (locate (m.g m.turn.tp).field m.turn.attackers []) blocks neg) = some g →
      Match.Moved r m (.block blocks neg) ⟨g, (m.turn.afterBlock (m.g (!m.turn.tp)).field blocks).prune g⟩
  | attack {k t neg sl g} : (m.g m.turn.tp).field[k]? = some sl →
      m.g.step? r (.attack m.turn.tp k t neg) = some g →
      Match.Moved r m (.attack k t neg) ⟨g, (m.turn.afterAttack r sl).prune g⟩
  | tap {k color sl out} : (m.g m.turn.tp).field[k]? = some sl → manaOut sl.card color = some out →
      Match.Moved r m (.tap k color) ⟨m.g, (m.turn.afterTap sl out).prune m.g⟩
  | oppTap {k color sl out} : (m.g (!m.turn.tp)).field[k]? = some sl → manaOut sl.card color = some out →
      Match.Moved r m (.oppTap k color) ⟨m.g, (m.turn.afterOppTap sl out).prune m.g⟩
  | endTurn {d} : Match.Moved r m .endTurn
      ⟨m.g.mend.drawUpTo r (!m.turn.tp) r.drawPerTurn,
       { m.turn.next with decked := d }.prune (m.g.mend.drawUpTo r (!m.turn.tp) r.drawPerTurn)⟩

theorem Match.step0?_moved {r : Rules} {m m' : Match} {ch : TChoice} (hs : m.step0? r ch = some m') :
    Match.Moved r m ch m' := by
  unfold Match.step0? at hs
  split at hs
  · cases hs
  cases ch with
  | place h i j up pay =>
    simp only at hs
    split at hs
    · cases hs
    · rename_i c hc
      split at hs
      · rename_i hok
        obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.1 hs
        exact .place hc hok hg
      · cases hs
  | cast h i j up pay =>
    simp only at hs
    split at hs
    · cases hs
    · rename_i c hc
      split at hs
      · rename_i hok
        obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.1 hs
        exact .cast hc hok hg
      · cases hs
  | resolve p k e apply neg tgt =>
    simp only at hs
    split at hs
    · obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.1 hs
      exact .resolve hg
    · cases hs
  | settle neg =>
    simp only [Option.some.injEq] at hs
    subst hs; exact .settle
  | pass => simp at hs
  | attack k t neg =>
    simp only at hs
    split at hs
    · cases hs
    · rename_i sl hsl
      split at hs
      · split at hs
        · split at hs
          · cases hs; exact .declare hsl
          · cases hs
        · split at hs
          · obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.1 hs
            exact .attack hsl hg
          · cases hs
      · cases hs
  | block blocks neg =>
    simp only at hs
    split at hs
    · obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.1 hs
      exact .block hg
    · cases hs
  | tap k color =>
    simp only at hs
    split at hs
    · cases hs
    · rename_i sl hsl
      split at hs
      · cases hs
      · rename_i out hout
        split at hs
        · cases hs; exact .tap hsl hout
        · cases hs
  | oppTap k color =>
    simp only at hs
    split at hs
    · cases hs
    · rename_i sl hsl
      split at hs
      · cases hs
      · rename_i out hout
        split at hs
        · cases hs; exact .oppTap hsl hout
        · cases hs
  | endTurn =>
    simp only at hs
    split at hs
    · cases hs; exact .endTurn
    · cases hs

@[simp] theorem TurnInfo.withPrio_tp (t : TurnInfo) (p n) : (t.withPrio p n).tp = t.tp := rfl
@[simp] theorem TurnInfo.withPrio_summons (t : TurnInfo) (p n) : (t.withPrio p n).summons = t.summons := rfl
@[simp] theorem TurnInfo.withPrio_placed (t : TurnInfo) (p n) : (t.withPrio p n).placed = t.placed := rfl
@[simp] theorem TurnInfo.withPrio_pool (t : TurnInfo) (p n) : (t.withPrio p n).pool = t.pool := rfl
@[simp] theorem TurnInfo.withPrio_oppPool (t : TurnInfo) (p n) : (t.withPrio p n).oppPool = t.oppPool := rfl
@[simp] theorem TurnInfo.withPrio_spent (t : TurnInfo) (p n) : (t.withPrio p n).spent = t.spent := rfl
@[simp] theorem TurnInfo.withPrio_made (t : TurnInfo) (p n) : (t.withPrio p n).made = t.made := rfl

theorem TurnInfo.prioAfter_eq (r : Rules) (before after : TurnInfo) (ch : TChoice) :
    ∃ p n, before.prioAfter r after ch = after.withPrio p n := by
  unfold TurnInfo.prioAfter
  split
  · exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩
  · split <;> exact ⟨_, _, rfl⟩

theorem TurnInfo.afterPass_eq (t : TurnInfo) : ∃ p n, t.afterPass = t.withPrio p n := by
  unfold TurnInfo.afterPass
  split
  · exact ⟨_, _, rfl⟩
  · split <;> exact ⟨_, _, rfl⟩

/-- 1歩は、優先権を考えない1歩（`Moved`。パスなら何も変えない）のあとに、優先権とパスの回数だけを変えたもの -/
theorem Match.step?_moved {r : Rules} {m m' : Match} {ch : TChoice} (hs : m.step? r ch = some m') :
    ∃ m0 p n, (ch = .pass ∧ m0 = m ∨ Match.Moved r m ch m0) ∧ m' = ⟨m0.g, m0.turn.withPrio p n⟩ := by
  unfold Match.step? at hs
  split at hs
  · rename_i m1 h1
    cases hs
    have hf : State.of (m1.g true) (m1.g false) = m1.g := State.fresh_eq _
    rw [hf]
    unfold Match.step1? at h1
    split at h1
    · cases h1
    · split at h1
      · split at h1
        · cases h1
          obtain ⟨p, n, hpn⟩ := m.turn.afterPass_eq
          exact ⟨m, p, n, .inl ⟨rfl, rfl⟩, by rw [hpn]⟩
        · cases h1
      · split at h1
        · obtain ⟨m2, h2, rfl⟩ := Option.map_eq_some_iff.1 h1
          obtain ⟨p, n, hpn⟩ := m.turn.prioAfter_eq r m2.turn ch
          exact ⟨m2, p, n, .inr (Match.step0?_moved h2), by simp only [hpn]⟩
        · cases h1
  · cases hs

/-- **優先権（公理）：パス・状態の確認・両者がパスしたあとの動き（解決・ブロック）以外の動きができたなら、
動いたのは優先権を持つプレイヤー** -/
theorem Match.step?_prio {r : Rules} {m m' : Match} {ch : TChoice} (hs : m.step? r ch = some m')
    (hp : ch ≠ .pass) (hn : ∀ neg, ch ≠ .settle neg) (ha : m.turn.afterPasses r ch = false) :
    ch.actor m.turn.tp = m.turn.prio := by
  unfold Match.step? at hs
  split at hs
  · rename_i m1 h1
    unfold Match.step1? at h1
    split at h1
    · cases h1
    · split at h1
      · exact absurd rfl hp
      · rename_i hnp
        split at h1
        · rename_i hok
          cases ch with
          | settle neg => exact absurd rfl (hn neg)
          | _ =>
            simp only [TurnInfo.prioOK, ha, Bool.false_eq_true, ite_false, Bool.and_eq_true, beq_iff_eq] at hok
            exact hok.2
        · cases h1
  · cases hs

/-! ## ターンのない対戦への引き継ぎ -/

theorem Reachable.drawUpTo {r : Rules} {decks : PlayerId → List Card} (p : PlayerId) :
    ∀ (n : Nat) {g : State}, Reachable r decks g → Reachable r decks (g.drawUpTo r p n)
  | 0, _, h => h
  | n + 1, g, h => by
    unfold State.drawUpTo
    split
    · rename_i g' hg
      exact Reachable.drawUpTo p n (h.step (step?_sound hg))
    · exact h

/-- **ターンのある対戦の盤面は、どれもターンのないモデルで到達できる盤面** -/
theorem TReachable.reachable {r : Rules} {decks : PlayerId → List Card} {first : PlayerId} {m : Match}
    (h : TReachable r decks first m) : Reachable r decks m.g := by
  induction h with
  | start =>
    simp only [Match.start]
    split
    · exact Reachable.drawUpTo first _ .start
    · exact .start
  | step ch _ hs ih =>
    obtain ⟨m0, _, _, ⟨-, rfl⟩ | hmv, rfl⟩ := Match.step?_moved hs
    · exact ih
    show Reachable r decks m0.g
    cases hmv with
    | place _ _ hg => exact ih.step (step?_sound hg)
    | cast _ _ hg => exact ih.step (step?_sound hg)
    | resolve hg => exact ih.step (step?_sound hg)
    | settle => exact ih.step (.settle _ _)
    | attack _ hg => exact ih.step (step?_sound hg)
    | declare _ => exact ih
    | block hg => exact ih.step (step?_sound hg)
    | tap _ _ => exact ih
    | oppTap _ _ => exact ih
    | endTurn => exact Reachable.drawUpTo _ _ (ih.step (.mend _))

/-- **ターンのない対戦のどの盤面でも成り立つ性質は、ターンのある対戦でも成り立つ**
（盤面の制約、★、受け入れた証明のジョブなど） -/
theorem TReachable.of_reachable {r : Rules} {decks : PlayerId → List Card} {first : PlayerId}
    {P : State → Prop} (hP : ∀ g, Reachable r decks g → P g) {m : Match}
    (h : TReachable r decks first m) : P m.g :=
  hP _ h.reachable

/-! ## ターンがあるから言える性質 -/

@[simp] theorem TurnInfo.prune_tp (t : TurnInfo) (g : State) : (t.prune g).tp = t.tp := rfl
@[simp] theorem TurnInfo.prune_summons (t : TurnInfo) (g : State) : (t.prune g).summons = t.summons := rfl
@[simp] theorem TurnInfo.prune_placed (t : TurnInfo) (g : State) : (t.prune g).placed = t.placed := rfl
@[simp] theorem TurnInfo.prune_pool (t : TurnInfo) (g : State) : (t.prune g).pool = t.pool := rfl
@[simp] theorem TurnInfo.prune_oppPool (t : TurnInfo) (g : State) : (t.prune g).oppPool = t.oppPool := rfl
@[simp] theorem TurnInfo.prune_made (t : TurnInfo) (g : State) : (t.prune g).made = t.made := rfl
@[simp] theorem TurnInfo.prune_spent (t : TurnInfo) (g : State) : (t.prune g).spent = t.spent := rfl
@[simp] theorem TurnInfo.pop_summons (r : Rules) (t : TurnInfo) : (t.pop r).summons = t.summons := by
  unfold TurnInfo.pop; split <;> rfl
@[simp] theorem TurnInfo.pop_placed (r : Rules) (t : TurnInfo) : (t.pop r).placed = t.placed := by
  unfold TurnInfo.pop; split <;> rfl
@[simp] theorem TurnInfo.pop_pool (r : Rules) (t : TurnInfo) : (t.pop r).pool = t.pool := by
  unfold TurnInfo.pop; split <;> rfl
@[simp] theorem TurnInfo.pop_oppPool (r : Rules) (t : TurnInfo) : (t.pop r).oppPool = t.oppPool := by
  unfold TurnInfo.pop; split <;> rfl
@[simp] theorem TurnInfo.pop_made (r : Rules) (t : TurnInfo) : (t.pop r).made = t.made := by
  unfold TurnInfo.pop; split <;> rfl
@[simp] theorem TurnInfo.pop_spent (r : Rules) (t : TurnInfo) : (t.pop r).spent = t.spent := by
  unfold TurnInfo.pop; split <;> rfl

/-- **1ターンに置いた戦闘できるカードの枚数は、上限を超えない**（上限があるとき） -/
theorem TReachable.summons_le {r : Rules} {decks : PlayerId → List Card} {first : PlayerId} {m : Match}
    (h : TReachable r decks first m) (hl : r.summonsPerTurn ≠ 0) : m.turn.summons ≤ r.summonsPerTurn := by
  induction h with
  | start => simp [Match.start]
  | step ch _ hs ih =>
    obtain ⟨m0, _, _, ⟨-, rfl⟩ | hmv, rfl⟩ := Match.step?_moved hs
    · simpa using ih
    simp only [TurnInfo.withPrio_summons]
    cases hmv with
    | @place _ _ _ _ _ c _ hc hok _ =>
      simp only [TurnInfo.placeOK, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
        beq_iff_eq, decide_eq_true_eq] at hok
      simp only [TurnInfo.prune_summons, TurnInfo.afterPlace]
      split
      · rename_i hf
        rcases hok.1.1.2 with (h1 | h1) | h1
        · simp [hf] at h1
        · exact absurd h1 hl
        · omega
      · simpa using ih
    | cast _ _ _ => simpa [TurnInfo.afterCast] using ih
    | resolve _ => simpa using ih
    | settle => simpa using ih
    | attack _ _ => simpa [TurnInfo.afterAttack] using ih
    | declare _ => simpa [TurnInfo.afterAttack] using ih
    | block _ => simpa [TurnInfo.afterBlock] using ih
    | tap _ _ => simpa [TurnInfo.afterTap] using ih
    | oppTap _ _ => simpa [TurnInfo.afterOppTap] using ih
    | endTurn => simp [TurnInfo.prune, TurnInfo.next]

/-- **種類ごとの上限：1ターンに置いた、その種類のカードの枚数は上限を超えない**（例：土地は1ターンに1枚） -/
theorem TReachable.placed_le {r : Rules} {decks : PlayerId → List Card} {first : PlayerId} {m : Match}
    (h : TReachable r decks first m) {l : PlaceLimit} (hl : l ∈ r.placeLimits) :
    (m.turn.placed.filter l.types.contains).length ≤ l.count := by
  induction h with
  | start => simp [Match.start]
  | step ch _ hs ih =>
    obtain ⟨m0, _, _, ⟨-, rfl⟩ | hmv, rfl⟩ := Match.step?_moved hs
    · simpa using ih
    simp only [TurnInfo.withPrio_placed]
    cases hmv with
    | @place _ _ _ _ _ c _ _ hok _ =>
      simp only [TurnInfo.placeOK, Bool.and_eq_true, List.all_eq_true] at hok
      have := hok.1.2 l hl
      simp only [TurnInfo.prune_placed, TurnInfo.afterPlace, List.filter_append, List.length_append]
      simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at this
      rcases this with h1 | h1
      · have : c.type ∉ l.types := by simpa using h1
        simpa [List.filter_cons, this] using ih
      · simp only [List.filter_cons, List.filter_nil]
        split <;> simp <;> omega
    | cast _ _ _ => simpa [TurnInfo.afterCast] using ih
    | resolve _ => simpa using ih
    | settle => simpa using ih
    | attack _ _ => simpa [TurnInfo.afterAttack] using ih
    | declare _ => simpa [TurnInfo.afterAttack] using ih
    | block _ => simpa [TurnInfo.afterBlock] using ih
    | tap _ _ => simpa [TurnInfo.afterTap] using ih
    | oppTap _ _ => simpa [TurnInfo.afterOppTap] using ih
    | endTurn => simp [TurnInfo.prune, TurnInfo.next]

/-- 記録はどれも、フィールドのカード（ダメージを除いたもの）の一部（同じカードの枚数も含めて） -/
def TurnInfo.Fits (t : TurnInfo) (g : State) : Prop :=
  BagLe t.attacked (g t.tp).bases ∧ BagLe t.entered (g t.tp).bases ∧ BagLe t.tapped (g t.tp).bases ∧
    BagLe t.oppTapped (g (!t.tp)).bases ∧ BagLe t.blocked (g (!t.tp)).bases ∧ BagLe t.attackers (g t.tp).bases

theorem TurnInfo.prune_fits (t : TurnInfo) (g : State) : (t.prune g).Fits g :=
  ⟨prune_bagLe _ _, prune_bagLe _ _, prune_bagLe _ _, prune_bagLe _ _, prune_bagLe _ _, prune_bagLe _ _⟩

/-- **攻撃・置いた・タップ・ブロック・攻撃の宣言の記録は、いつもフィールドのカードの一部**
（同じカードの枚数も含めて。だから、フィールドのどのカードも1ターンに1回までしか攻撃できず、
タップしているカードは、起きるまでタップできない） -/
theorem TReachable.fits {r : Rules} {decks : PlayerId → List Card} {first : PlayerId} {m : Match}
    (h : TReachable r decks first m) : m.turn.Fits m.g := by
  induction h with
  | start => refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro a <;> simp [Match.start]
  | step ch _ hs ih =>
    obtain ⟨m0, _, _, ⟨-, rfl⟩ | hmv, rfl⟩ := Match.step?_moved hs
    · exact ih
    show m0.turn.Fits m0.g
    cases hmv <;> exact TurnInfo.prune_fits _ _

/-- **攻撃したカードの記録は、ターンプレイヤーのフィールドのカードの一部**
（同じカードの枚数も含めて。だから、フィールドのどのカードも1ターンに1回までしか攻撃できない） -/
theorem TReachable.attacked_bagLe {r : Rules} {decks : PlayerId → List Card} {first : PlayerId} {m : Match}
    (h : TReachable r decks first m) : BagLe m.turn.attacked (m.g m.turn.tp).bases :=
  h.fits.1

/-! ## マナの収支 -/

theorem bagLeB_count {l m : List String} (h : bagLeB l m = true) (a : String) : l.count a ≤ m.count a := by
  by_cases ha : a ∈ l
  · have := List.all_eq_true.1 h a ha
    simpa using this
  · rw [List.count_eq_zero_of_not_mem ha]; exact Nat.zero_le _

theorem length_foldl_erase : ∀ (l m : List String), (∀ a, l.count a ≤ m.count a) →
    (l.foldl List.erase m).length + l.length = m.length
  | [], m, _ => by simp
  | a :: l, m, h => by
    have ha : a ∈ m := List.count_pos_iff.1 (Nat.lt_of_lt_of_le (by simp) (h a))
    have h' : ∀ b, l.count b ≤ (m.erase a).count b := by
      intro b
      have := h b
      rw [List.count_erase, List.count_cons] at *
      by_cases hb : a = b
      · subst hb; simp at this ⊢; omega
      · have : (a == b) = false := by simpa using hb
        simp_all
    have := length_foldl_erase l (m.erase a) h'
    simp only [List.foldl_cons, List.length_cons, List.length_erase_of_mem ha] at this ⊢
    have := List.length_pos_of_mem ha
    omega

/-- 払ったあとのマナの数 -/
theorem length_pay {c : Card} {pool pay : List String} (h : payOK c pool pay = true) :
    (pay.foldl List.erase pool).length + pay.length = pool.length := by
  simp only [payOK, Bool.and_eq_true] at h
  exact length_foldl_erase pay pool (bagLeB_count h.1.1)

/-- **マナの収支：持っているマナと、払ったマナの合計は、このターンにタップで出したマナに等しい**
（だから、1ターンに払うマナは、そのターンにタップして出したマナを超えない） -/
theorem TReachable.mana_balance {r : Rules} {decks : PlayerId → List Card} {first : PlayerId} {m : Match}
    (h : TReachable r decks first m) : m.turn.pool.length + m.turn.oppPool.length + m.turn.spent = m.turn.made := by
  induction h with
  | start => simp [Match.start]
  | step ch _ hs ih =>
    obtain ⟨m0, _, _, ⟨-, rfl⟩ | hmv, rfl⟩ := Match.step?_moved hs
    · simpa using ih
    simp only [TurnInfo.withPrio_pool, TurnInfo.withPrio_oppPool, TurnInfo.withPrio_spent, TurnInfo.withPrio_made]
    cases hmv with
    | place _ hok _ =>
      simp only [TurnInfo.placeOK, Bool.and_eq_true] at hok
      have := length_pay hok.2
      simp only [TurnInfo.prune_pool, TurnInfo.prune_oppPool, TurnInfo.prune_spent, TurnInfo.prune_made,
        TurnInfo.afterPlace]
      omega
    | cast _ hok _ =>
      simp only [TurnInfo.castOK, Bool.and_eq_true] at hok
      have := length_pay hok.2
      simp only [TurnInfo.prune_pool, TurnInfo.prune_oppPool, TurnInfo.prune_spent, TurnInfo.prune_made,
        TurnInfo.afterCast]
      omega
    | resolve _ => simpa using ih
    | settle => simpa using ih
    | attack _ _ => simpa [TurnInfo.afterAttack] using ih
    | declare _ => simpa [TurnInfo.afterAttack] using ih
    | block _ => simpa [TurnInfo.afterBlock] using ih
    | tap _ _ => simp [TurnInfo.afterTap]; omega
    | oppTap _ _ => simp [TurnInfo.afterOppTap]; omega
    | endTurn => simp [TurnInfo.prune, TurnInfo.next]

/-- **1ターンに払ったマナは、そのターンにタップして出したマナを超えない** -/
theorem TReachable.spent_le {r : Rules} {decks : PlayerId → List Card} {first : PlayerId} {m : Match}
    (h : TReachable r decks first m) : m.turn.spent ≤ m.turn.made := by
  have := h.mana_balance; omega

end CardGen

namespace CardGen

/-! ## 優先権・スタック・対戦の終わり・ターンの終わりの性質 -/

theorem TurnInfo.afterPass_passes (t : TurnInfo) (h : t.passes < 2) : t.afterPass.passes ≤ 2 := by
  unfold TurnInfo.afterPass TurnInfo.withPrio
  split
  · simp only; omega
  · split <;> simp

theorem TurnInfo.prioAfter_passes (r : Rules) (b a : TurnInfo) (ch : TChoice) (h : b.passes ≤ 2) :
    (b.prioAfter r a ch).passes ≤ 2 := by
  unfold TurnInfo.prioAfter TurnInfo.withPrio
  split
  · simpa using h
  · simp
  · split <;> simp

/-- **パスの回数はいつも 2 以下**（両者がパスしたら、解決かブロックをするまでパスできない） -/
theorem TReachable.passes_le {r : Rules} {decks : PlayerId → List Card} {first : PlayerId} {m : Match}
    (h : TReachable r decks first m) : m.turn.passes ≤ 2 := by
  induction h with
  | start => simp [Match.start]
  | @step m m' ch _ hs ih =>
    unfold Match.step? at hs
    split at hs
    · rename_i m1 h1
      cases hs
      show m1.turn.passes ≤ 2
      unfold Match.step1? at h1
      split at h1
      · cases h1
      · split at h1
        · split at h1
          · rename_i hlt; cases h1; exact m.turn.afterPass_passes hlt
          · cases h1
        · split at h1
          · obtain ⟨m2, _, rfl⟩ := Option.map_eq_some_iff.1 h1
            exact m.turn.prioAfter_passes r m2.turn ch ih
          · cases h1
    · cases hs

/-- スタックの記録の、残ったものはどれもフィールドにある -/
theorem pruneStack_mem : ∀ (st : List (PlayerId × Slot)) (f : PlayerId → List Slot),
    ∀ e ∈ pruneStack st f, e.2 ∈ f e.1
  | [], _, e, he => by simp [pruneStack] at he
  | (q, a) :: as, f, e, he => by
    unfold pruneStack at he
    split at he
    · rename_i ha
      rcases List.mem_cons.1 he with rfl | he
      · exact ha
      · have := pruneStack_mem as _ e he
        by_cases hq : e.1 = q
        · simp only [hq, ite_true] at this
          exact hq ▸ List.mem_of_mem_erase this
        · simpa [hq] using this
    · exact pruneStack_mem as f e he

/-- スタックの記録が、どれもフィールドのカード -/
def TurnInfo.StackFits (t : TurnInfo) (g : State) : Prop := ∀ e ∈ t.stack, e.2 ∈ (g e.1).bases

theorem TurnInfo.prune_stackFits (t : TurnInfo) (g : State) : (t.prune g).StackFits g :=
  fun e he => pruneStack_mem t.stack (fun q => (g q).bases) e he

/-- **スタックに積まれたカードは、いつも置いたプレイヤーのフィールド（スタックのゾーン）にある**
（打ち消されたり、手札に戻されたりしたカードは、スタックからも消える） -/
theorem TReachable.stack_fits {r : Rules} {decks : PlayerId → List Card} {first : PlayerId} {m : Match}
    (h : TReachable r decks first m) : m.turn.StackFits m.g := by
  induction h with
  | start => intro e he; simp [Match.start] at he
  | step ch _ hs ih =>
    obtain ⟨m0, _, _, ⟨-, rfl⟩ | hmv, rfl⟩ := Match.step?_moved hs
    · exact ih
    show m0.turn.StackFits m0.g
    cases hmv <;> exact TurnInfo.prune_stackFits _ _

/-- **対戦が終わったら（ライフが 0 か、デッキ切れ）、それ以上どの動きもできない** -/
theorem Match.step?_over {r : Rules} {m : Match} (h : m.over r = true) (ch : TChoice) : m.step? r ch = none := by
  unfold Match.step? Match.step1?
  simp [h]

/-- 引いても、フィールドは変わらない -/
theorem State.drawUpTo_field (r : Rules) (p : PlayerId) :
    ∀ (n : Nat) (g : State) (q : PlayerId), ((g.drawUpTo r p n) q).field = (g q).field
  | 0, _, _ => rfl
  | n + 1, g, q => by
    unfold State.drawUpTo
    cases hg : g.step? r (.draw p) with
    | none => rfl
    | some g' =>
      simp only
      rw [State.drawUpTo_field r p n g' q]
      unfold State.step? at hg
      split at hg
      · rename_i g0 h0
        cases hg
        simp only [State.step0?] at h0
        split at h0
        · cases h0; cases q <;> cases p <;> rfl
        · cases h0
      · cases hg

/-- **ターンの終わりに、どのカードの受けたダメージとターンの終わりまでの変化も消える**
（新しいターンの始めには、フィールドのどのカードもダメージが 0 で、攻撃力・守備力の一時的な変化もない） -/
theorem Match.endTurn_clean {r : Rules} {m m' : Match} (hs : m.step? r .endTurn = some m') :
    ∀ q, ∀ sl ∈ (m'.g q).field, sl.base = sl := by
  obtain ⟨m0, _, _, ⟨h, -⟩ | hmv, rfl⟩ := Match.step?_moved hs
  · cases h
  cases hmv
  intro q sl hsl
  simp only [State.drawUpTo_field, State.mend, State.map_apply, List.mem_map] at hsl
  obtain ⟨x, -, rfl⟩ := hsl
  rfl

end CardGen

namespace CardGen

/-! ## マナの色 -/

/-- マナ `c` は、カードの一覧 `cards` のどれかのマナを出すカードが出せる色（`""` は無色） -/
def ManaFrom (cards : List Card) (c : String) : Prop :=
  ∃ card ∈ cards, 0 < card.mana ∧ (c = card.manaColor ∨ c ∈ card.manaChoice)

theorem mem_of_mem_foldl_erase : ∀ (l m : List String) (c : String), c ∈ l.foldl List.erase m → c ∈ m
  | [], _, _, h => h
  | a :: l, m, c, h => List.mem_of_mem_erase (mem_of_mem_foldl_erase l (m.erase a) c h)

theorem manaOut_from {card : Card} {color : String} {out : List String} (h : manaOut card color = some out) :
    ∀ c ∈ out, 0 < card.mana ∧ (c = card.manaColor ∨ c ∈ card.manaChoice) := by
  intro c hc
  unfold manaOut at h
  split at h
  · cases h
    obtain ⟨h1, h2⟩ := List.mem_replicate.1 hc
    exact ⟨Nat.pos_of_ne_zero h1, .inl h2⟩
  · split at h
    · rename_i hch
      cases h
      obtain ⟨h1, rfl⟩ := List.mem_replicate.1 hc
      exact ⟨Nat.pos_of_ne_zero h1, .inr (by simpa using hch)⟩
    · cases h

/-- **持っているマナは、どれも一覧のマナを出すカードが出せる色（か無色）**
（形式の検査で、カードの出すマナの色はルールのマナの色のどれかなので、マナはルールの色か無色だけ） -/
theorem TReachable.mana_from {r : Rules} {decks : PlayerId → List Card} {first : PlayerId} {pool : List Card}
    (hpool : ∀ p, ∀ x ∈ decks p, x ∈ pool) {m : Match} (h : TReachable r decks first m) :
    ∀ c ∈ m.turn.pool ++ m.turn.oppPool, ManaFrom pool c := by
  induction h with
  | start => intro c hc; simp [Match.start] at hc
  | @step m _ ch hm hs ih =>
    obtain ⟨m0, _, _, ⟨-, rfl⟩ | hmv, rfl⟩ := Match.step?_moved hs
    · simpa [TurnInfo.withPrio] using ih
    simp only [TurnInfo.withPrio_pool, TurnInfo.withPrio_oppPool]
    have fp := hm.reachable.fromPool hpool
    cases hmv with
    | place _ _ _ =>
      intro c hc
      simp only [TurnInfo.prune_pool, TurnInfo.prune_oppPool, TurnInfo.afterPlace, List.mem_append] at hc
      rcases hc with hc | hc
      · exact ih c (List.mem_append_left _ (mem_of_mem_foldl_erase _ _ _ hc))
      · exact ih c (List.mem_append_right _ hc)
    | cast _ _ _ =>
      intro c hc
      simp only [TurnInfo.prune_pool, TurnInfo.prune_oppPool, TurnInfo.afterCast, List.mem_append] at hc
      rcases hc with hc | hc
      · exact ih c (List.mem_append_left _ hc)
      · exact ih c (List.mem_append_right _ (mem_of_mem_foldl_erase _ _ _ hc))
    | @tap _ _ sl _ hsl hout =>
      intro c hc
      simp only [TurnInfo.prune_pool, TurnInfo.prune_oppPool, TurnInfo.afterTap, List.mem_append] at hc
      rcases hc with (hc | hc) | hc
      · exact ih c (List.mem_append_left _ hc)
      · exact ⟨sl.card, fp.field (List.mem_of_getElem? hsl), manaOut_from hout c hc⟩
      · exact ih c (List.mem_append_right _ hc)
    | @oppTap _ _ sl _ hsl hout =>
      intro c hc
      simp only [TurnInfo.prune_pool, TurnInfo.prune_oppPool, TurnInfo.afterOppTap, List.mem_append] at hc
      rcases hc with hc | hc | hc
      · exact ih c (List.mem_append_left _ hc)
      · exact ih c (List.mem_append_right _ hc)
      · exact ⟨sl.card, fp.field (List.mem_of_getElem? hsl), manaOut_from hout c hc⟩
    | endTurn => intro c hc; simp [TurnInfo.prune, TurnInfo.next] at hc
    | resolve _ => simpa using ih
    | settle => simpa using ih
    | attack _ _ => simpa [TurnInfo.afterAttack] using ih
    | declare _ => simpa [TurnInfo.afterAttack] using ih
    | block _ => simpa [TurnInfo.afterBlock] using ih

end CardGen
