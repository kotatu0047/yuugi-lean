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
定理は `TurnProps.lean` にある。
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

end CardGen
