import CardGen.IR

/-!
# 中間表現のゲームのモデル

★（ルールから導く性質）が「どの盤面でも」成り立つことを述べるための、小さな対戦のモデル。
ターンやフェイズは持たず、どちらのプレイヤーもいつでも次の動きをしてよいとする
（実際の対戦より多くの動きを許すので、ここで証明した性質は実際の対戦でも成り立つ）。

- ドロー：デッキの一番上を手札に加える
- 置く：手札のカードを、その種類を置けるゾーンに置く（「1枚まで」のゾーンは空きがあるときだけ）
- 発動して解決する：フィールドの、発動する効果を持つカードを取り除き、効果の動き（破壊・手札に戻す・
  ドロー）を順に行い
  （無効にされていれば何もしない）、そのカードを墓地へ送る

カードの持ち主とコントロールするプレイヤーは同じで、カードは持ち主の側から出ない。
-/

namespace CardGen
open Lean

/-- フィールドのゾーン（デッキ・墓地以外）に置かれたカード -/
structure Slot where
  /-- `Rules.zones` の何番目のゾーンか -/
  zone : Nat
  card : Card
  faceUp : Bool
deriving Repr, DecidableEq

/-- 1人分の状態 -/
structure PState where
  deck : List Card
  hand : List Card
  grave : List Card
  field : List Slot
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

def Slot.view (sl : Slot) (mine : Bool) : View :=
  { type := sl.card.type, tags := sl.card.tags, mine, faceUp := sl.faceUp, isSelf := false }

/-- フィールド上の、範囲に合うカードをすべて破壊して墓地へ送る（`mine`：効果の持ち主の側か） -/
def PState.destroy (r : Rules) (sel : Selector) (mine : Bool) (s : PState) : PState :=
  let hit := fun sl : Slot => r.onFieldZone sl.zone && sel.matches (sl.view mine)
  { s with field := s.field.filter (fun sl => !hit sl),
           grave := s.grave ++ (s.field.filter hit).map (·.card) }

/-- フィールド上の、範囲に合うカードをすべて手札に戻す -/
def PState.bounce (r : Rules) (sel : Selector) (mine : Bool) (s : PState) : PState :=
  let hit := fun sl : Slot => r.onFieldZone sl.zone && sel.matches (sl.view mine)
  { s with field := s.field.filter (fun sl => !hit sl),
           hand := s.hand ++ (s.field.filter hit).map (·.card) }

/-- デッキから `n` 枚引く（足りなければある分だけ） -/
def PState.drawN (n : Nat) (s : PState) : PState :=
  { s with deck := s.deck.drop n, hand := s.hand ++ s.deck.take n }

/-- プレイヤー `p` の効果の動きを1つ行う -/
def State.applyAction (r : Rules) (p : PlayerId) (g : State) : Action → State
  | .destroy sel => fun q => (g q).destroy r sel (q == p)
  | .bounce sel => fun q => (g q).bounce r sel (q == p)
  | .draw n => g.set p ((g p).drawN n)

/-- プレイヤー `p` が、フィールドの `k` 番目のカード `sl` の効果（動き `as`）を発動して解決したあとの状態 -/
def State.resolve (r : Rules) (p : PlayerId) (g : State) (k : Nat) (sl : Slot) (as : List Action)
    (apply : Bool) : State :=
  let g1 := g.set p { g p with field := (g p).field.eraseIdx k }
  let g2 := if apply then as.foldl (State.applyAction r p) g1 else g1
  g2.set p { g2 p with grave := (g2 p).grave ++ [sl.card] }

/-- 対戦の1つの動き -/
inductive Step (r : Rules) : State → State → Prop
  | draw (g : State) (p : PlayerId) (c : Card) (d : List Card) :
      (g p).deck = c :: d →
      Step r g (g.set p { g p with deck := d, hand := (g p).hand ++ [c] })
  | place (g : State) (p : PlayerId) (c : Card) (i : Nat) (z : Zone) (up : Bool) :
      c ∈ (g p).hand → r.zones[i]? = some z → z.role = .plain → z.admits.contains c.type →
      (z.capacity = .one → ((g p).field.filter (·.zone == i)).length < z.count) →
      Step r g (g.set p { g p with hand := (g p).hand.erase c, field := (g p).field ++ [⟨i, c, up⟩] })
  | resolve (g : State) (p : PlayerId) (k : Nat) (sl : Slot) (as : List Action) (apply : Bool) :
      (g p).field[k]? = some sl → .activated as ∈ sl.card.effects →
      Step r g (g.resolve r p k sl as apply)

/-- ゲーム開始時の状態：それぞれのデッキから初期手札を引いた状態 -/
def start (r : Rules) (decks : PlayerId → List Card) : State :=
  fun p => { deck := (decks p).drop r.handSize, hand := (decks p).take r.handSize, grave := [], field := [] }

/-- 開始時の状態から動きを繰り返して到達できる -/
inductive Reachable (r : Rules) (decks : PlayerId → List Card) : State → Prop
  | start : Reachable r decks (start r decks)
  | step {g g'} : Reachable r decks g → Step r g g' → Reachable r decks g'

end CardGen
