import CardGen.IR

/-!
# 中間表現のゲームのモデル

★（ルールから導く性質）が「どの盤面でも」成り立つことを述べるための、小さな対戦のモデル。
ターンやフェイズは持たず、どちらのプレイヤーもいつでも次の動きをしてよいとする
（実際の対戦より多くの動きを許すので、ここで証明した性質は実際の対戦でも成り立つ）。

- ドロー：デッキの一番上を手札に加える
- 置く：手札のカードを、その種類を置けるゾーンのマスに置く（「1枚まで」のゾーンは空いているマスだけ）
- 発動して解決する：フィールドの、発動する効果を持つカードを取り除き、効果の動き（破壊・手札に戻す・
  ドロー・ダメージ・回復）を順に行い（無効にされていれば何もしない）、そのカードを墓地へ送る
- 攻撃する：表側表示の戦闘できるカードで、相手の戦闘できるカードを攻撃する（相手に戦闘できるカードが
  なければ直接攻撃する）。攻撃力は、元の攻撃力に、無効にされていない「攻撃力を変える」効果を足したもの。
  どのカードが無効かは動きの引数で受け取り、どんな組み合わせも許す（無効の判定は `Negation.lean`）
  - 表側表示のカードどうしは攻撃力を比べ、低い方を破壊し、差をそのコントローラーへのダメージにする
    （同じなら両方を破壊する。ともに 0 なら何も起きない）
  - 裏側表示のカードは守備力で受け、攻撃力が高ければ破壊し、低ければ差を攻撃した側へのダメージにする
  - MTG 式の戦闘（`Rules.blocking`）では、相手に戦闘できるカードがいても直接攻撃でき（ブロックされなかったとき）、
    ブロックされたら互いの攻撃力をダメージとして与え、守備力以上のダメージを受けた方を破壊する

カードの持ち主とコントロールするプレイヤーは同じで、カードは持ち主の側から出ない。
-/

namespace CardGen
open Lean

/-- フィールドのゾーン（デッキ・墓地以外）に置かれたカード -/
structure Slot where
  /-- `Rules.zones` の何番目のゾーンか -/
  zone : Nat
  /-- ゾーンの何番目のマスか -/
  cell : Nat
  card : Card
  faceUp : Bool
deriving Repr, DecidableEq

/-- 1人分の状態 -/
structure PState where
  deck : List Card
  hand : List Card
  grave : List Card
  field : List Slot
  life : Nat
deriving Repr, DecidableEq

/-- プレイヤー（`true` と `false` の2人） -/
abbrev PlayerId := Bool

/-- 対戦の状態 -/
abbrev State := PlayerId → PState

def State.set (g : State) (p : PlayerId) (s : PState) : State :=
  fun q => if q = p then s else g q

@[simp] theorem State.set_same (g : State) (p s) : g.set p s p = s := by simp [State.set]
@[simp] theorem State.set_other (g : State) {p q : PlayerId} (s) (h : q ≠ p) : g.set p s q = g q := by
  simp [State.set, h]

/-- 1人分のカードの枚数 -/
def PState.size (s : PState) : Nat := s.deck.length + s.hand.length + s.grave.length + s.field.length

/-- `i` 番目のゾーンが「フィールド上」に数えるゾーンか（デッキ・墓地の役割のゾーンは数えない） -/
def Rules.onFieldZone (r : Rules) (i : Nat) : Bool :=
  match r.zones[i]? with
  | some z => z.role == .plain && z.onField
  | none => false

/-- `q` のフィールドのカード `sl` の、盤面のマス目の位置（マス目の上にないゾーンなら `none`）。
`false` のプレイヤーのマスは、点対称の位置 -/
def Rules.cellOf (r : Rules) (q : PlayerId) (sl : Slot) : Option Cell :=
  match r.zones[sl.zone]? with
  | some z => (z.cells[sl.cell]?).map fun c => if q then c else c.flip
  | none => none

/-- 効果を出したもの：効果の持ち主と、効果を持つカードのマス -/
structure Src where
  p : PlayerId
  cell : Option Cell
deriving Repr, DecidableEq

def Cell.adjacentOpt : Option Cell → Option Cell → Bool
  | some a, some b => a.adjacent b
  | _, _ => false

def Cell.sameColumnOpt : Option Cell → Option Cell → Bool
  | some a, some b => a.col == b.col
  | _, _ => false

/-- `q` のフィールドのカード `sl` を、効果を出したもの `src` から見た情報 -/
def Slot.view (r : Rules) (sl : Slot) (q : PlayerId) (src : Src) : View :=
  let c := r.cellOf q sl
  { type := sl.card.type, tags := sl.card.tags, mine := q == src.p, faceUp := sl.faceUp, isSelf := false,
    adjacent := Cell.adjacentOpt src.cell c, sameColumn := Cell.sameColumnOpt src.cell c }

/-- `q` のフィールド上の、範囲に合うカードをすべて破壊して墓地へ送る -/
def PState.destroy (r : Rules) (sel : Selector) (q : PlayerId) (src : Src) (s : PState) : PState :=
  let hit := fun sl : Slot => r.onFieldZone sl.zone && sel.matches (sl.view r q src)
  { s with field := s.field.filter (fun sl => !hit sl),
           grave := s.grave ++ (s.field.filter hit).map (·.card) }

/-- `q` のフィールド上の、範囲に合うカードをすべて手札に戻す -/
def PState.bounce (r : Rules) (sel : Selector) (q : PlayerId) (src : Src) (s : PState) : PState :=
  let hit := fun sl : Slot => r.onFieldZone sl.zone && sel.matches (sl.view r q src)
  { s with field := s.field.filter (fun sl => !hit sl),
           hand := s.hand ++ (s.field.filter hit).map (·.card) }

/-- デッキから `n` 枚引く（足りなければある分だけ） -/
def PState.drawN (n : Nat) (s : PState) : PState :=
  { s with deck := s.deck.drop n, hand := s.hand ++ s.deck.take n }

/-- ダメージを受ける（ライフは 0 より下がらない） -/
def PState.damage (n : Nat) (s : PState) : PState := { s with life := s.life - n }

/-- 効果を出したもの `src`（持ち主 `src.p`）の効果の動きを1つ行う -/
def State.applyAction (r : Rules) (src : Src) (g : State) : Action → State
  | .destroy sel => fun q => (g q).destroy r sel q src
  | .bounce sel => fun q => (g q).bounce r sel q src
  | .draw n => g.set src.p ((g src.p).drawN n)
  | .damage n => g.set (!src.p) ((g (!src.p)).damage n)
  | .heal n => g.set src.p { g src.p with life := (g src.p).life + n }

/-- プレイヤー `p` が、フィールドの `k` 番目のカード `sl` の効果（動き `as`）を発動して解決したあとの状態。
マスの関係は、カードが置かれていたマスから見る -/
def State.resolve (r : Rules) (p : PlayerId) (g : State) (k : Nat) (sl : Slot) (as : List Action)
    (apply : Bool) : State :=
  let g1 := g.set p { g p with field := (g p).field.eraseIdx k }
  let g2 := if apply then as.foldl (State.applyAction r ⟨p, r.cellOf p sl⟩) g1 else g1
  g2.set p { g2 p with grave := (g2 p).grave ++ [sl.card] }

/-! ## 戦闘 -/

/-- フィールドのカードの位置（プレイヤーと、`field` の何番目か） -/
abbrev Pos := PlayerId × Nat

/-- `q` のフィールドの `j` 番目のカード `src` の効果で、位置 `t` のカード `tsl` の攻撃力が変わる量。
`neg` は効果が無効になっているカードの位置 -/
def boostFrom (r : Rules) (neg : List Pos) (t : Pos) (tsl : Slot) (q : PlayerId) (j : Nat) (src : Slot) : Int :=
  if src.faceUp && r.onFieldZone src.zone && !neg.contains (q, j) then
    (src.card.effects.map fun
      | .boost sel n =>
        if sel.matches { tsl.view r t.1 ⟨q, r.cellOf q src⟩ with isSelf := (q, j) == t } then n else 0
      | _ => 0).sum
  else 0

/-- `q` のフィールドのカード全体から、位置 `t` のカードの攻撃力が変わる量 -/
def State.boostSide (r : Rules) (g : State) (neg : List Pos) (t : Pos) (tsl : Slot) (q : PlayerId) : Int :=
  ((List.range (g q).field.length).map fun j =>
    match (g q).field[j]? with
    | some src => boostFrom r neg t tsl q j src
    | none => 0).sum

/-- 位置 `t` のカード `tsl` の攻撃力 -/
def State.atkOf (r : Rules) (g : State) (neg : List Pos) (t : Pos) (tsl : Slot) : Nat :=
  (Int.ofNat tsl.card.attack + g.boostSide r neg t tsl true + g.boostSide r neg t tsl false).toNat

/-- 戦闘できる「フィールド上」のカードか -/
def Rules.fights (r : Rules) (sl : Slot) : Bool := r.onFieldZone sl.zone && r.fighters.contains sl.card.type

/-- フィールドの `k` 番目のカードを破壊して墓地へ送る -/
def PState.destroyAt (k : Nat) (s : PState) : PState :=
  match s.field[k]? with
  | some sl => { s with field := s.field.eraseIdx k, grave := s.grave ++ [sl.card] }
  | none => s

/-- `p` のフィールドの `k` 番目のカード `sl` で、相手のフィールドの `target` 番目のカード
（`none` なら直接）を攻撃したあとの状態 -/
def State.battle (r : Rules) (g : State) (neg : List Pos) (p : PlayerId) (k : Nat) (sl : Slot) :
    Option Nat → State
  | none => g.set (!p) ((g (!p)).damage (g.atkOf r neg (p, k) sl))
  | some j =>
    match (g (!p)).field[j]? with
    | none => g
    | some tl =>
      let a := g.atkOf r neg (p, k) sl
      if r.blocking then
        -- MTG 式：互いの攻撃力をダメージとして与え、守備力以上のダメージを受けた方を破壊する（プレイヤーへのダメージはない）
        let b := g.atkOf r neg (!p, j) tl
        let g1 := if 0 < b ∧ sl.card.defense ≤ b then g.set p ((g p).destroyAt k) else g
        if 0 < a ∧ tl.card.defense ≤ a then g1.set (!p) ((g1 (!p)).destroyAt j) else g1
      else if tl.faceUp then
        let t := g.atkOf r neg (!p, j) tl
        if t < a then g.set (!p) (((g (!p)).destroyAt j).damage (a - t))
        else if a < t then g.set p (((g p).destroyAt k).damage (t - a))
        else if a = 0 then g
        else (g.set p ((g p).destroyAt k)).set (!p) ((g (!p)).destroyAt j)
      else
        let d := tl.card.defense
        if d < a then g.set (!p) ((g (!p)).destroyAt j)
        else if a < d then g.set p ((g p).damage (d - a))
        else g

/-- 対戦の1つの動き -/
inductive Step (r : Rules) : State → State → Prop
  | draw (g : State) (p : PlayerId) (c : Card) (d : List Card) :
      (g p).deck = c :: d →
      Step r g (g.set p { g p with deck := d, hand := (g p).hand ++ [c] })
  | place (g : State) (p : PlayerId) (c : Card) (i j : Nat) (z : Zone) (up : Bool) :
      c ∈ (g p).hand → r.zones[i]? = some z → z.role = .plain → z.admits.contains c.type → j < z.count →
      (z.capacity = .one → ∀ sl ∈ (g p).field, ¬(sl.zone = i ∧ sl.cell = j)) →
      Step r g (g.set p { g p with hand := (g p).hand.erase c, field := (g p).field ++ [⟨i, j, c, up⟩] })
  | resolve (g : State) (p : PlayerId) (k : Nat) (sl : Slot) (as : List Action) (apply : Bool) :
      (g p).field[k]? = some sl → .activated as ∈ sl.card.effects →
      Step r g (g.resolve r p k sl as apply)
  | attack (g : State) (p : PlayerId) (k : Nat) (sl : Slot) (target : Option Nat) (neg : List Pos) :
      (g p).field[k]? = some sl → sl.faceUp → r.fights sl →
      (match target with
       | none => r.blocking ∨ (g (!p)).field.all (!r.fights ·)
       | some j => ∃ tl, (g (!p)).field[j]? = some tl ∧ r.fights tl) →
      Step r g (g.battle r neg p k sl target)

/-- ゲーム開始時の状態：それぞれのデッキから初期手札を引いた状態 -/
def start (r : Rules) (decks : PlayerId → List Card) : State :=
  fun p => { deck := (decks p).drop r.handSize, hand := (decks p).take r.handSize, grave := [], field := [],
             life := r.life }

/-- 開始時の状態から動きを繰り返して到達できる -/
inductive Reachable (r : Rules) (decks : PlayerId → List Card) : State → Prop
  | start : Reachable r decks (start r decks)
  | step {g g'} : Reachable r decks g → Step r g g' → Reachable r decks g'

end CardGen
