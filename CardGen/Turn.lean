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

**ターンのある対戦の盤面は、どれもターンのないモデルで到達できる盤面**（`TReachable.reachable`）。
1歩はどれも `Step` の0回以上の繰り返しになるからである。そのため、盤面の制約（`Reachable.inv`）、
★（`derived_valid`・`gameClaims_valid`）、受け入れた証明のジョブは、ターンのある対戦でもそのまま成り立つ
（`TReachable.of_reachable`）。そのうえで、ターンがあるから言える性質（`TReachable.summons_le` など）を示す。
-/

namespace CardGen

/-- 攻撃したカードの記録を、今のフィールドにあるものだけに絞る。同じカードが複数あれば、フィールドにある枚数まで残す -/
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

/-- ターンの情報 -/
structure TurnInfo where
  /-- ターンプレイヤー -/
  tp : PlayerId
  /-- 何ターン目か（1 から） -/
  count : Nat := 1
  /-- このターンに置いた、戦闘できる種類のカードの枚数 -/
  summons : Nat := 0
  /-- このターンに攻撃したカード（ターンプレイヤーのフィールドにあるものだけ） -/
  attacked : List Slot := []
deriving Repr, DecidableEq

/-- ターンのある対戦の状態 -/
structure Match where
  g : State
  turn : TurnInfo

/-- ターンのある対戦の動き -/
inductive TChoice
  /-- ターンプレイヤーが手札の `hand` 番目のカードを `zone` 番目のゾーンに置く -/
  | place (hand : Nat) (zone : Nat) (up : Bool)
  /-- `p` がフィールドの `k` 番目のカードの `eff` 番目の効果を発動して解決する（どちらのターンでもよい） -/
  | resolve (p : PlayerId) (k : Nat) (eff : Nat) (apply : Bool)
  /-- ターンプレイヤーがフィールドの `k` 番目のカードで攻撃する -/
  | attack (k : Nat) (target : Option Nat) (neg : List Pos)
  /-- ターンを終え、相手のターンにする -/
  | endTurn
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

/-- 攻撃したカードの記録を、新しい盤面に合わせる -/
def TurnInfo.prune (t : TurnInfo) (g : State) : TurnInfo := { t with attacked := CardGen.prune t.attacked (g t.tp).field }

/-- 選んだ動きをしたあとの状態（できない動きなら `none`） -/
def Match.step? (r : Rules) (m : Match) : TChoice → Option Match
  | .place h i up => do
    let p := m.turn.tp
    let c ← (m.g p).hand[h]?
    let fighter := r.fights ⟨i, c, up⟩
    guard (!fighter || r.summonsPerTurn == 0 || decide (m.turn.summons < r.summonsPerTurn))
    let g ← m.g.step? r (.place p h i up)
    return ⟨g, { m.turn with summons := m.turn.summons + (if fighter then 1 else 0) }⟩
  | .resolve p k e apply => do
    let g ← m.g.step? r (.resolve p k e apply)
    return ⟨g, m.turn.prune g⟩
  | .attack k t neg => do
    let p := m.turn.tp
    let sl ← (m.g p).field[k]?
    guard (r.firstTurnAttack || m.turn.count != 1)
    guard (decide (m.turn.attacked.count sl < (m.g p).field.count sl))
    let g ← m.g.step? r (.attack p k t neg)
    return ⟨g, { m.turn with attacked := sl :: m.turn.attacked }.prune g⟩
  | .endTurn =>
    let p := !m.turn.tp
    some ⟨m.g.drawUpTo r p r.drawPerTurn, { tp := p, count := m.turn.count + 1 }⟩

/-- 開始時の状態から、`step?` を繰り返して到達できる -/
inductive TReachable (r : Rules) (decks : PlayerId → List Card) (first : PlayerId) : Match → Prop
  | start : TReachable r decks first (Match.start r decks first)
  | step {m m'} (ch : TChoice) : TReachable r decks first m → m.step? r ch = some m' → TReachable r decks first m'

/-! ## 1歩の中身 -/

theorem Match.step?_place {r : Rules} {m m' : Match} {h i : Nat} {up : Bool}
    (hs : m.step? r (.place h i up) = some m') :
    ∃ c, (m.g m.turn.tp).hand[h]? = some c ∧
      (r.fights ⟨i, c, up⟩ = false ∨ r.summonsPerTurn = 0 ∨ m.turn.summons < r.summonsPerTurn) ∧
      m.g.step? r (.place m.turn.tp h i up) = some m'.g ∧
      m'.turn = { m.turn with summons := m.turn.summons + (if r.fights ⟨i, c, up⟩ then 1 else 0) } := by
  simp only [Match.step?, Option.bind_eq_bind] at hs
  cases hc : (m.g m.turn.tp).hand[h]? with
  | none => simp [hc] at hs
  | some c =>
    simp only [hc, Option.bind_some] at hs
    cases hb : (!r.fights ⟨i, c, up⟩ || r.summonsPerTurn == 0 || decide (m.turn.summons < r.summonsPerTurn))
    · rw [hb] at hs
      simp only [guard, Bool.false_eq_true, ite_false] at hs
      cases hs
    · rw [hb] at hs
      cases hg : m.g.step? r (.place m.turn.tp h i up) with
      | none => simp [hg, guard] at hs
      | some g =>
        simp only [hg, guard, ite_true, Option.pure_def, Option.bind_some, Option.some.injEq] at hs
        subst hs
        refine ⟨c, rfl, ?_, rfl, rfl⟩
        simpa [or_assoc] using hb

theorem Match.step?_resolve {r : Rules} {m m' : Match} {p : PlayerId} {k e : Nat} {apply : Bool}
    (hs : m.step? r (.resolve p k e apply) = some m') :
    m.g.step? r (.resolve p k e apply) = some m'.g ∧ m'.turn = m.turn.prune m'.g := by
  simp only [Match.step?, Option.bind_eq_bind] at hs
  cases hg : m.g.step? r (.resolve p k e apply) with
  | none => simp [hg] at hs
  | some g =>
    simp only [hg, Option.pure_def, Option.bind_some, Option.some.injEq] at hs
    subst hs
    exact ⟨rfl, rfl⟩

theorem Match.step?_attack {r : Rules} {m m' : Match} {k : Nat} {t : Option Nat} {neg : List Pos}
    (hs : m.step? r (.attack k t neg) = some m') :
    ∃ sl, (m.g m.turn.tp).field[k]? = some sl ∧
      m.g.step? r (.attack m.turn.tp k t neg) = some m'.g ∧
      m'.turn = { m.turn with attacked := sl :: m.turn.attacked }.prune m'.g := by
  simp only [Match.step?, Option.bind_eq_bind] at hs
  cases hc : (m.g m.turn.tp).field[k]? with
  | none => simp [hc] at hs
  | some sl =>
    simp only [hc, Option.bind_some] at hs
    cases hb1 : (r.firstTurnAttack || m.turn.count != 1)
    · rw [hb1] at hs
      simp only [guard, Bool.false_eq_true, ite_false] at hs
      cases hs
    · rw [hb1] at hs
      simp only [guard, ite_true, Option.pure_def, Option.bind_some] at hs
      cases hb2 : decide (m.turn.attacked.count sl < (m.g m.turn.tp).field.count sl)
      · rw [hb2] at hs
        simp only [Bool.false_eq_true, ite_false] at hs
        cases hs
      · rw [hb2] at hs
        cases hg : m.g.step? r (.attack m.turn.tp k t neg) with
        | none => simp [hg] at hs
        | some g =>
          simp only [hg, ite_true, Option.bind_some, Option.some.injEq] at hs
          subst hs
          exact ⟨sl, rfl, rfl, rfl⟩

theorem Match.step?_endTurn {r : Rules} {m m' : Match} (hs : m.step? r .endTurn = some m') :
    m'.g = m.g.drawUpTo r (!m.turn.tp) r.drawPerTurn ∧
      m'.turn = { tp := !m.turn.tp, count := m.turn.count + 1 } := by
  simp only [Match.step?, Option.some.injEq] at hs
  subst hs
  exact ⟨rfl, rfl⟩

/-- 置く動きをすると、置いたプレイヤーのフィールドの最後に1枚加わる -/
theorem State.step?_place_field {r : Rules} {g g' : State} {p : PlayerId} {h i : Nat} {up : Bool} {c : Card}
    (hc : (g p).hand[h]? = some c) (hg : g.step? r (.place p h i up) = some g') :
    (g' p).field = (g p).field ++ [⟨i, c, up⟩] := by
  simp only [State.step?, hc, Option.bind_eq_bind, Option.bind_some, Option.bind_eq_some_iff] at hg
  obtain ⟨_, _, _, _, hg⟩ := hg
  simp only [Option.pure_def, Option.some.injEq] at hg
  subst hg
  simp [State.set]

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
    cases ch with
    | place h i up =>
      obtain ⟨_, _, _, hg, _⟩ := Match.step?_place hs
      exact ih.step (step?_sound hg)
    | resolve p k e apply => exact ih.step (step?_sound (Match.step?_resolve hs).1)
    | attack k t neg =>
      obtain ⟨_, _, hg, _⟩ := Match.step?_attack hs
      exact ih.step (step?_sound hg)
    | endTurn =>
      rw [(Match.step?_endTurn hs).1]
      exact Reachable.drawUpTo _ _ ih

/-- **ターンのない対戦のどの盤面でも成り立つ性質は、ターンのある対戦でも成り立つ**
（盤面の制約、★、受け入れた証明のジョブなど） -/
theorem TReachable.of_reachable {r : Rules} {decks : PlayerId → List Card} {first : PlayerId}
    {P : State → Prop} (hP : ∀ g, Reachable r decks g → P g) {m : Match}
    (h : TReachable r decks first m) : P m.g :=
  hP _ h.reachable

/-! ## ターンがあるから言える性質 -/

/-- **1ターンに置いた戦闘できるカードの枚数は、上限を超えない**（上限があるとき） -/
theorem TReachable.summons_le {r : Rules} {decks : PlayerId → List Card} {first : PlayerId} {m : Match}
    (h : TReachable r decks first m) (hl : r.summonsPerTurn ≠ 0) : m.turn.summons ≤ r.summonsPerTurn := by
  induction h with
  | start => simp [Match.start]
  | step ch _ hs ih =>
    cases ch with
    | place h i up =>
      obtain ⟨c, _, hok, _, ht⟩ := Match.step?_place hs
      rw [ht]
      by_cases hf : r.fights ⟨i, c, up⟩ = true
      · simp only [hf, ite_true]
        simp only [hf, hl, Bool.true_eq_false, false_or] at hok
        omega
      · simp only [hf]
        simpa using ih
    | resolve p k e apply => rw [(Match.step?_resolve hs).2]; exact ih
    | attack k t neg =>
      obtain ⟨_, _, _, ht⟩ := Match.step?_attack hs
      rw [ht]; exact ih
    | endTurn => rw [(Match.step?_endTurn hs).2]; simp

/-- **攻撃したカードの記録は、ターンプレイヤーのフィールドにあるカードの一部**
（同じカードの枚数も含めて。だから、フィールドのどのカードも1ターンに1回までしか攻撃できない） -/
theorem TReachable.attacked_bagLe {r : Rules} {decks : PlayerId → List Card} {first : PlayerId} {m : Match}
    (h : TReachable r decks first m) : BagLe m.turn.attacked (m.g m.turn.tp).field := by
  induction h with
  | start => intro a; simp [Match.start]
  | step ch _ hs ih =>
    rename_i m m'
    cases ch with
    | place h i up =>
      obtain ⟨c, hc, _, hg, ht⟩ := Match.step?_place hs
      rw [ht]
      -- 置くとターンプレイヤーのフィールドの最後に1枚加わる
      have hf := State.step?_place_field hc hg
      intro a
      have := ih a
      simp only [hf, List.count_append]
      omega
    | resolve p k e apply => rw [(Match.step?_resolve hs).2]; exact prune_bagLe _ _
    | attack k t neg =>
      obtain ⟨_, _, _, ht⟩ := Match.step?_attack hs
      rw [ht]; exact prune_bagLe _ _
    | endTurn => rw [(Match.step?_endTurn hs).2]; intro a; simp

end CardGen
