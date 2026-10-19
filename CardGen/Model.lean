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
  - 裏側表示のカードの守備力も、無効にされていない「守備力を変える」効果を足したもの
- MTG 式の戦闘（`Rules.blocking`、`State.combat`）：攻撃するカード（何枚でもよい）と、それぞれをブロックするカード
  （1枚の攻撃に何枚でもよい）を受け取る。ブロックされなかった攻撃は、攻撃力のダメージを相手に与える。
  ブロックされた攻撃は、攻撃力のダメージをブロックしたカードに順に割り振り（前のカードに破壊できるだけ与えてから次へ。
  最後のカードには残りすべて）、ブロックしたカードは攻撃力のダメージを攻撃したカードに与える
- カードが受けたダメージは、カードに残る（`Slot.damage`）。ダメージを受けたあと、守備力以上のダメージを受けている
  戦闘できるカードを破壊する（`State.sweep`）。ダメージを消す動き（`mend`）はいつでもできる（ターンのある対戦では
  ターンの終わりに行う）

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
  /-- 受けているダメージ（MTG 式の戦闘とカードへのダメージで増え、ターンの終わりに 0 に戻る） -/
  damage : Nat := 0
deriving Repr, DecidableEq

/-- ダメージを除いた、カードの置き場所・カード・向き -/
def Slot.base (sl : Slot) : Slot := { sl with damage := 0 }

@[simp] theorem Slot.base_damage (sl : Slot) (n : Nat) : Slot.base { sl with damage := n } = sl.base := rfl
@[simp] theorem Slot.base_base (sl : Slot) : sl.base.base = sl.base := rfl
@[simp] theorem Slot.base_zone (sl : Slot) : sl.base.zone = sl.zone := rfl
@[simp] theorem Slot.base_cell (sl : Slot) : sl.base.cell = sl.cell := rfl
@[simp] theorem Slot.base_card (sl : Slot) : sl.base.card = sl.card := rfl
@[simp] theorem Slot.base_faceUp (sl : Slot) : sl.base.faceUp = sl.faceUp := rfl

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

/-! ## 攻撃力と守備力 -/

/-- フィールドのカードの位置（プレイヤーと、`field` の何番目か） -/
abbrev Pos := PlayerId × Nat

/-- 攻撃力を変える効果 -/
def Effect.atkMod : Effect → Option (Selector × Int)
  | .boost s n => some (s, n)
  | _ => none

/-- 守備力を変える効果 -/
def Effect.defMod : Effect → Option (Selector × Int)
  | .toughen s n => some (s, n)
  | _ => none

/-- `q` のフィールドの `j` 番目のカード `src` の効果（`pick` で選んだ種類）で、位置 `t` のカード `tsl` の値が変わる量。
`neg` は効果が無効になっているカードの位置 -/
def modFrom (r : Rules) (pick : Effect → Option (Selector × Int)) (neg : List Pos) (t : Pos) (tsl : Slot)
    (q : PlayerId) (j : Nat) (src : Slot) : Int :=
  if src.faceUp && r.onFieldZone src.zone && !neg.contains (q, j) then
    (src.card.effects.map fun e =>
      match pick e with
      | some (sel, n) =>
        if sel.matches { tsl.view r t.1 ⟨q, r.cellOf q src⟩ with isSelf := (q, j) == t } then n else 0
      | none => 0).sum
  else 0

/-- `q` のフィールドのカード全体から、位置 `t` のカードの値が変わる量 -/
def State.modSide (r : Rules) (g : State) (pick : Effect → Option (Selector × Int)) (neg : List Pos) (t : Pos)
    (tsl : Slot) (q : PlayerId) : Int :=
  ((List.range (g q).field.length).map fun j =>
    match (g q).field[j]? with
    | some src => modFrom r pick neg t tsl q j src
    | none => 0).sum

/-- 位置 `t` のカード `tsl` の攻撃力 -/
def State.atkOf (r : Rules) (g : State) (neg : List Pos) (t : Pos) (tsl : Slot) : Nat :=
  (Int.ofNat tsl.card.attack + g.modSide r Effect.atkMod neg t tsl true +
    g.modSide r Effect.atkMod neg t tsl false).toNat

/-- 位置 `t` のカード `tsl` の守備力 -/
def State.defOf (r : Rules) (g : State) (neg : List Pos) (t : Pos) (tsl : Slot) : Nat :=
  (Int.ofNat tsl.card.defense + g.modSide r Effect.defMod neg t tsl true +
    g.modSide r Effect.defMod neg t tsl false).toNat

/-- 戦闘できる「フィールド上」のカードか -/
def Rules.fights (r : Rules) (sl : Slot) : Bool := r.onFieldZone sl.zone && r.fighters.contains sl.card.type

/-! ## カードへのダメージ -/

/-- フィールドの `i` 番目のカードに、ダメージ `d i` を加える -/
def PState.mark (d : Nat → Nat) (s : PState) : PState :=
  { s with field := s.field.mapIdx fun i sl => { sl with damage := sl.damage + d i } }

/-- フィールドの `i` 番目のカード `sl` のうち、`dead i sl` のものを破壊して墓地へ送る -/
def PState.sweep (dead : Nat → Slot → Bool) (s : PState) : PState :=
  { s with field := (s.field.zipIdx.filter fun x => !dead x.2 x.1).map (·.1),
           grave := s.grave ++ (s.field.zipIdx.filter fun x => dead x.2 x.1).map (·.1.card) }

/-- 位置 `(q, i)` のカード `sl` が、守備力以上のダメージを受けている戦闘できるカードか -/
def State.lethal (r : Rules) (g : State) (neg : List Pos) (q : PlayerId) (i : Nat) (sl : Slot) : Bool :=
  r.fights sl && decide (0 < sl.damage) && decide (g.defOf r neg (q, i) sl ≤ sl.damage)

/-- 守備力以上のダメージを受けている戦闘できるカードを、すべて破壊する -/
def State.sweep (r : Rules) (g : State) (neg : List Pos) : State := fun q => (g q).sweep (g.lethal r neg q)

/-- どのカードのダメージも 0 に戻す -/
def State.mend (g : State) : State := fun q => { g q with field := (g q).field.map Slot.base }

/-- `negS`（無効になっているカード）の、今の盤面での位置 -/
def State.negAt (g : State) (negS : List (PlayerId × Slot)) : List Pos :=
  [true, false].flatMap fun q =>
    ((List.range (g q).field.length).filter fun i =>
      ((g q).field[i]?.map fun sl => negS.contains (q, sl.base)).getD false).map (q, ·)

/-- 効果を出したもの `src` の「カードへのダメージ」：範囲に合う戦闘できるカードすべてに `n` のダメージ -/
def State.strike (r : Rules) (sel : Selector) (n : Nat) (src : Src) (negS : List (PlayerId × Slot)) (g : State) :
    State :=
  let g1 : State := fun q => (g q).mark fun i =>
    match (g q).field[i]? with
    | some sl => if r.fights sl && sel.matches (sl.view r q src) then n else 0
    | none => 0
  g1.sweep r (g1.negAt negS)

/-- 効果を出したもの `src`（持ち主 `src.p`）の効果の動きを1つ行う。`negS`：効果が無効になっているカード -/
def State.applyAction (r : Rules) (src : Src) (negS : List (PlayerId × Slot)) (g : State) : Action → State
  | .destroy sel => fun q => (g q).destroy r sel q src
  | .bounce sel => fun q => (g q).bounce r sel q src
  | .draw n => g.set src.p ((g src.p).drawN n)
  | .damage n => g.set (!src.p) ((g (!src.p)).damage n)
  | .heal n => g.set src.p { g src.p with life := (g src.p).life + n }
  | .strike sel n => g.strike r sel n src negS

/-- 位置の一覧 `neg` の、盤面 `g` のカード -/
def State.negSlots (g : State) (neg : List Pos) : List (PlayerId × Slot) :=
  neg.filterMap fun (q, i) => ((g q).field[i]?).map fun sl => (q, sl.base)

/-- プレイヤー `p` が、フィールドの `k` 番目のカード `sl` の効果（動き `as`）を発動して解決したあとの状態。
マスの関係は、カードが置かれていたマスから見る。`neg`：効果が無効になっているカードの位置（解決する前の盤面で） -/
def State.resolve (r : Rules) (p : PlayerId) (g : State) (k : Nat) (sl : Slot) (as : List Action)
    (apply : Bool) (neg : List Pos := []) : State :=
  let g1 := g.set p { g p with field := (g p).field.eraseIdx k }
  let g2 := if apply then as.foldl (State.applyAction r ⟨p, r.cellOf p sl⟩ (g.negSlots neg)) g1 else g1
  g2.set p { g2 p with grave := (g2 p).grave ++ [sl.card] }

/-! ## 戦闘 -/

/-- フィールドの `k` 番目のカードを破壊して墓地へ送る -/
def PState.destroyAt (k : Nat) (s : PState) : PState :=
  match s.field[k]? with
  | some sl => { s with field := s.field.eraseIdx k, grave := s.grave ++ [sl.card] }
  | none => s

/-- 遊戯王式の戦闘：`p` のフィールドの `k` 番目のカード `sl` で、相手のフィールドの `target` 番目のカード
（`none` なら直接）を攻撃したあとの状態 -/
def State.duel (r : Rules) (g : State) (neg : List Pos) (p : PlayerId) (k : Nat) (sl : Slot) :
    Option Nat → State
  | none => g.set (!p) ((g (!p)).damage (g.atkOf r neg (p, k) sl))
  | some j =>
    match (g (!p)).field[j]? with
    | none => g
    | some tl =>
      let a := g.atkOf r neg (p, k) sl
      if tl.faceUp then
        let t := g.atkOf r neg (!p, j) tl
        if t < a then g.set (!p) (((g (!p)).destroyAt j).damage (a - t))
        else if a < t then g.set p (((g p).destroyAt k).damage (t - a))
        else if a = 0 then g
        else (g.set p ((g p).destroyAt k)).set (!p) ((g (!p)).destroyAt j)
      else
        let d := g.defOf r neg (!p, j) tl
        if d < a then g.set (!p) ((g (!p)).destroyAt j)
        else if a < d then g.set p ((g p).damage (d - a))
        else g

/-- ブロックしたカード `tls`（位置とカード）に、攻撃力 `rem` のダメージを順に割り振る -/
def State.assign (r : Rules) (g : State) (neg : List Pos) (o : PlayerId) : Nat → List (Nat × Slot) → List (Nat × Nat)
  | _, [] => []
  | rem, [(j, _)] => [(j, rem)]
  | rem, (j, tl) :: rest =>
    let x := min rem (g.defOf r neg (o, j) tl - tl.damage)
    (j, x) :: State.assign r g neg o (rem - x) rest

/-- 攻撃するカード1枚（`p` のフィールドの `k` 番目、ブロックしたのは相手のフィールドの `bs` 番目のカード）の
ダメージ：（攻撃側のカードへのダメージ、守る側のカードへのダメージ、相手へのダメージ） -/
def State.fight1 (r : Rules) (g : State) (neg : List Pos) (p : PlayerId) (k : Nat) (bs : List Nat) :
    List (Nat × Nat) × List (Nat × Nat) × Nat :=
  match (g p).field[k]? with
  | none => ([], [], 0)
  | some sl =>
    let a := g.atkOf r neg (p, k) sl
    let tls := bs.filterMap fun j => ((g (!p)).field[j]?).map (j, ·)
    if tls.isEmpty then ([], [], a)
    else ([(k, (tls.map fun (j, tl) => g.atkOf r neg (!p, j) tl).sum)], g.assign r neg (!p) a tls, 0)

/-- 位置ごとのダメージの一覧から、`i` 番目のカードへのダメージの合計 -/
def sumAt (l : List (Nat × Nat)) (i : Nat) : Nat := ((l.filter (·.1 == i)).map (·.2)).sum

/-- MTG 式の戦闘：`p` のフィールドの `atk` 番目のカードたちで攻撃し、相手のフィールドの `j` 番目のカードが
`atk` の `a` 番目の攻撃をブロックする（`blocks` の `(j, a)`）。ダメージは同時に与える -/
def State.combat (r : Rules) (g : State) (neg : List Pos) (p : PlayerId) (atk : List Nat) (blocks : List (Nat × Nat)) :
    State :=
  let parts := atk.zipIdx.map fun (k, a) =>
    g.fight1 r neg p k ((blocks.filter fun (b : Nat × Nat) => b.2 == a).map Prod.fst)
  let dA := parts.flatMap (·.1)
  let dB := parts.flatMap (·.2.1)
  let hit := (parts.map (·.2.2)).sum
  let g1 := (g.set p ((g p).mark (sumAt dA))).set (!p) (((g (!p)).mark (sumAt dB)).damage hit)
  g1.sweep r neg

/-- MTG 式の戦闘の、攻撃とブロックのカードの条件（攻撃は表側表示の戦闘できるカード、ブロックは戦闘できるカード） -/
def State.combatOK (r : Rules) (g : State) (p : PlayerId) (atk : List Nat) (blocks : List (Nat × Nat)) : Bool :=
  atk.all (fun k => ((g p).field[k]?.map fun sl => sl.faceUp && r.fights sl).getD false) &&
  blocks.all (fun b => ((g (!p)).field[b.1]?.map r.fights).getD false && decide (b.2 < atk.length))

/-- `p` のフィールドの `k` 番目のカード `sl` で、相手のフィールドの `target` 番目のカード
（`none` なら直接）を攻撃したあとの状態（MTG 式の戦闘なら、ブロックされたかどうか） -/
def State.battle (r : Rules) (g : State) (neg : List Pos) (p : PlayerId) (k : Nat) (sl : Slot) (t : Option Nat) :
    State :=
  if r.blocking then g.combat r neg p [k] (t.map (·, 0)).toList else g.duel r neg p k sl t

/-- 対戦の1つの動き -/
inductive Step (r : Rules) : State → State → Prop
  | draw (g : State) (p : PlayerId) (c : Card) (d : List Card) :
      (g p).deck = c :: d →
      Step r g (g.set p { g p with deck := d, hand := (g p).hand ++ [c] })
  | place (g : State) (p : PlayerId) (c : Card) (i j : Nat) (z : Zone) (up : Bool) :
      c ∈ (g p).hand → r.zones[i]? = some z → z.role = .plain → z.admits.contains c.type → j < z.count →
      (z.capacity = .one → ∀ sl ∈ (g p).field, ¬(sl.zone = i ∧ sl.cell = j)) →
      Step r g (g.set p { g p with hand := (g p).hand.erase c, field := (g p).field ++ [⟨i, j, c, up, 0⟩] })
  | resolve (g : State) (p : PlayerId) (k : Nat) (sl : Slot) (as : List Action) (apply : Bool) (neg : List Pos) :
      (g p).field[k]? = some sl → .activated as ∈ sl.card.effects →
      Step r g (g.resolve r p k sl as apply neg)
  | attack (g : State) (p : PlayerId) (k : Nat) (sl : Slot) (target : Option Nat) (neg : List Pos) :
      (g p).field[k]? = some sl → sl.faceUp → r.fights sl →
      (match target with
       | none => r.blocking ∨ (g (!p)).field.all (!r.fights ·)
       | some j => ∃ tl, (g (!p)).field[j]? = some tl ∧ r.fights tl) →
      Step r g (g.battle r neg p k sl target)
  | combat (g : State) (p : PlayerId) (atk : List Nat) (blocks : List (Nat × Nat)) (neg : List Pos) :
      g.combatOK r p atk blocks → Step r g (g.combat r neg p atk blocks)
  | mend (g : State) : Step r g g.mend

/-- ゲーム開始時の状態：それぞれのデッキから初期手札を引いた状態 -/
def start (r : Rules) (decks : PlayerId → List Card) : State :=
  fun p => { deck := (decks p).drop r.handSize, hand := (decks p).take r.handSize, grave := [], field := [],
             life := r.life }

/-- 開始時の状態から動きを繰り返して到達できる -/
inductive Reachable (r : Rules) (decks : PlayerId → List Card) : State → Prop
  | start : Reachable r decks (start r decks)
  | step {g g'} : Reachable r decks g → Step r g g' → Reachable r decks g'

end CardGen
