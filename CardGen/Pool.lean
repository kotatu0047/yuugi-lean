import CardGen.Claims

/-!
# 盤面のカードはカードの一覧から来る・ライフの上限

動き（ドロー・置く・発動・攻撃）はどれもカードを移すだけなので、カードの一覧から作ったデッキで始めれば、
到達できるどの状態でも、どのプレイヤーのところにあるカードも一覧のカードである（`Reachable.fromPool`）。

これを使うと、カードの一覧によって決まる★を証明できる。

| 型 | 規則 |
|---|---|
| F. ライフ | 一覧に「回復」の動きを持つカードがなければ、ライフは初期ライフを超えない（`Reachable.life_le`） |
-/

namespace CardGen

/-- 1人分の状態にあるカード -/
def PState.cards (s : PState) : List Card := s.deck ++ s.hand ++ s.grave ++ s.field.map (·.card)

theorem PState.mem_cards {s : PState} {x : Card} :
    x ∈ s.cards ↔ x ∈ s.deck ∨ x ∈ s.hand ∨ x ∈ s.grave ∨ ∃ sl ∈ s.field, sl.card = x := by
  simp [PState.cards]

/-- 動きの後のどのプレイヤーのカードも、動きの前にそのプレイヤーのところにあった -/
def CardsSub (g g' : State) : Prop := ∀ q, ∀ x ∈ (g' q).cards, x ∈ (g q).cards

theorem CardsSub.refl (g : State) : CardsSub g g := fun _ _ h => h

theorem CardsSub.trans {a b c : State} (h1 : CardsSub a b) (h2 : CardsSub b c) : CardsSub a c :=
  fun q x hx => h1 q x (h2 q x hx)

/-- 1人分だけ変える -/
theorem CardsSub.set {g : State} {p : PlayerId} {s : PState} (h : ∀ x ∈ s.cards, x ∈ (g p).cards) :
    CardsSub g (g.set p s) := by
  intro q x hx
  by_cases hq : q = p
  · subst hq; rw [State.set_same] at hx; exact h x hx
  · rwa [State.set_other _ _ hq] at hx

theorem cards_destroy (r : Rules) (sel : Selector) (q : PlayerId) (src : Src) (s : PState) :
    ∀ x ∈ (s.destroy r sel q src).cards, x ∈ s.cards := by
  intro x hx
  simp only [PState.mem_cards, PState.destroy, List.mem_append, List.mem_map, List.mem_filter] at hx ⊢
  rcases hx with h | h | (h | ⟨sl, ⟨hsl, _⟩, rfl⟩) | ⟨sl, ⟨hsl, _⟩, rfl⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl h))
  · exact .inr (.inr (.inr ⟨sl, hsl, rfl⟩))
  · exact .inr (.inr (.inr ⟨sl, hsl, rfl⟩))

theorem cards_bounce (r : Rules) (sel : Selector) (q : PlayerId) (src : Src) (s : PState) :
    ∀ x ∈ (s.bounce r sel q src).cards, x ∈ s.cards := by
  intro x hx
  simp only [PState.mem_cards, PState.bounce, List.mem_append, List.mem_map, List.mem_filter] at hx ⊢
  rcases hx with h | (h | ⟨sl, ⟨hsl, _⟩, rfl⟩) | h | ⟨sl, ⟨hsl, _⟩, rfl⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inr ⟨sl, hsl, rfl⟩))
  · exact .inr (.inr (.inl h))
  · exact .inr (.inr (.inr ⟨sl, hsl, rfl⟩))

theorem cards_counter (r : Rules) (sel : Selector) (q : PlayerId) (src : Src) (s : PState) :
    ∀ x ∈ (s.counter r sel q src).cards, x ∈ s.cards := by
  intro x hx
  simp only [PState.mem_cards, PState.counter, List.mem_append, List.mem_map, List.mem_filter] at hx ⊢
  rcases hx with h | h | (h | ⟨sl, ⟨hsl, _⟩, rfl⟩) | ⟨sl, ⟨hsl, _⟩, rfl⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl h))
  · exact .inr (.inr (.inr ⟨sl, hsl, rfl⟩))
  · exact .inr (.inr (.inr ⟨sl, hsl, rfl⟩))

theorem cards_pump (d : Nat → Int × Int) (s : PState) : ∀ x ∈ (s.pump d).cards, x ∈ s.cards := by
  have : (s.pump d).field.map (·.card) = s.field.map (·.card) := by
    have := congrArg (List.map Slot.card) (PState.map_base_pump d s)
    simpa [List.map_map, Function.comp_def] using this
  intro x hx
  simp only [PState.cards, List.mem_append] at hx ⊢
  rw [this] at hx
  exact hx

theorem cards_drawN (n : Nat) (s : PState) : ∀ x ∈ (s.drawN n).cards, x ∈ s.cards := by
  intro x hx
  simp only [PState.mem_cards, PState.drawN, List.mem_append] at hx ⊢
  rcases hx with h | (h | h) | h | h
  · exact .inl (List.mem_of_mem_drop h)
  · exact .inr (.inl h)
  · exact .inl (List.mem_of_mem_take h)
  · exact .inr (.inr (.inl h))
  · exact .inr (.inr (.inr h))

theorem cards_damage (n : Nat) (s : PState) : ∀ x ∈ (s.damage n).cards, x ∈ s.cards := fun _ h => h

theorem cards_destroyAt (k : Nat) (s : PState) : ∀ x ∈ (s.destroyAt k).cards, x ∈ s.cards := by
  intro x hx
  unfold PState.destroyAt at hx
  split at hx
  · rename_i sl hk
    simp only [PState.mem_cards, List.mem_append, List.mem_singleton] at hx ⊢
    rcases hx with h | h | (h | rfl) | ⟨sl', hsl, rfl⟩
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl h))
    · exact .inr (.inr (.inr ⟨sl, List.mem_of_getElem? hk, rfl⟩))
    · exact .inr (.inr (.inr ⟨sl', (List.eraseIdx_sublist _ _).subset hsl, rfl⟩))
  · exact hx

theorem cards_mark (d : Nat → Nat) (s : PState) : ∀ x ∈ (s.mark d).cards, x ∈ s.cards := by
  have : (s.mark d).field.map (·.card) = s.field.map (·.card) := by
    have := congrArg (List.map Slot.card) (PState.map_base_mark d s)
    simpa [List.map_map, Function.comp_def] using this
  intro x hx
  simp only [PState.cards, List.mem_append] at hx ⊢
  rw [this] at hx
  exact hx

theorem cards_sweep (dead : Nat → Slot → Bool) (s : PState) : ∀ x ∈ (s.sweep dead).cards, x ∈ s.cards := by
  intro x hx
  simp only [PState.mem_cards, PState.sweep, List.mem_append, List.mem_map, List.mem_filter] at hx ⊢
  have hf : ∀ y : Slot × Nat, y ∈ s.field.zipIdx → y.1 ∈ s.field := fun y hy => by
    have := List.mem_map_of_mem (f := Prod.fst) hy
    rwa [List.zipIdx_map_fst] at this
  rcases hx with h | h | (h | ⟨y, ⟨hy, _⟩, rfl⟩) | ⟨sl, ⟨y, ⟨hy, _⟩, rfl⟩, rfl⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl h))
  · exact .inr (.inr (.inr ⟨y.1, hf y hy, rfl⟩))
  · exact .inr (.inr (.inr ⟨y.1, hf y hy, rfl⟩))

/-- 各プレイヤーの状態を変える -/
theorem CardsSub.map {g : State} {f : PlayerId → PState → PState} (h : ∀ q, ∀ x ∈ (f q (g q)).cards, x ∈ (g q).cards) :
    CardsSub g (g.map f) := by
  intro q x hx; rw [State.map_apply] at hx; exact h q x hx

theorem cardsSub_sweep (r : Rules) (g : State) (neg : List Pos) : CardsSub g (g.sweep r neg) :=
  CardsSub.map fun q => cards_sweep _ (g q)

theorem cardsSub_mend (g : State) : CardsSub g g.mend := by
  refine CardsSub.map fun q x hx => ?_
  simp only [PState.cards, List.map_map, List.mem_append] at hx ⊢
  exact hx

theorem cardsSub_strike (r : Rules) (sel : Selector) (n : Nat) (src : Src) (negS : List (PlayerId × Slot))
    (g : State) : CardsSub g (g.strike r sel n src negS) :=
  have h : CardsSub g (g.strikeMarks r sel n src) := CardsSub.map fun q => cards_mark _ (g q)
  h.trans (cardsSub_sweep _ _ _)

theorem cardsSub_pumpAll (r : Rules) (sel : Selector) (a d : Int) (src : Src) (negS : List (PlayerId × Slot))
    (g : State) : CardsSub g (g.pumpAll r sel a d src negS) :=
  have h : CardsSub g (g.pumpMarks r sel a d src) := CardsSub.map fun q => cards_pump _ (g q)
  h.trans (cardsSub_sweep _ _ _)

theorem cardsSub_applyAction (r : Rules) (src : Src) (negS : List (PlayerId × Slot)) (g : State) (a : Action) :
    CardsSub g (g.applyAction r src negS a) := by
  cases a with
  | destroy sel => exact CardsSub.map fun q => cards_destroy r sel q src (g q)
  | bounce sel => exact CardsSub.map fun q => cards_bounce r sel q src (g q)
  | draw n => exact CardsSub.set (cards_drawN n (g src.p))
  | damage n => exact CardsSub.set (cards_damage n (g (!src.p)))
  | heal n => exact CardsSub.set fun _ h => h
  | strike sel n => exact cardsSub_strike r sel n src negS g
  | pump sel a d => exact cardsSub_pumpAll r sel a d src negS g
  | counter sel => exact CardsSub.map fun q => cards_counter r sel q src (g q)

theorem cardsSub_foldl (r : Rules) (src : Src) (negS : List (PlayerId × Slot)) (as : List Action) (g : State) :
    CardsSub g (as.foldl (State.applyAction r src negS) g) := by
  induction as generalizing g with
  | nil => exact CardsSub.refl g
  | cons a t ih => exact (cardsSub_applyAction r src negS g a).trans (ih _)

theorem cardsSub_duel (r : Rules) (g : State) (neg : List Pos) (p : PlayerId) (k : Nat) (sl : Slot)
    (t : Option Nat) : CardsSub g (g.duel r neg p k sl t) := by
  have dd : ∀ (j n : Nat) (s : PState), ∀ x ∈ ((s.destroyAt j).damage n).cards, x ∈ s.cards :=
    fun j n s x hx => cards_destroyAt j s x (cards_damage n _ x hx)
  cases t with
  | none => exact CardsSub.set (cards_damage _ _)
  | some j =>
    simp only [State.duel]
    split
    · exact CardsSub.refl g
    · split
      · split
        · exact CardsSub.set (dd _ _ _)
        · split
          · exact CardsSub.set (dd _ _ _)
          · split
            · exact CardsSub.refl g
            · have hne : (!p) ≠ p := by cases p <;> decide
              refine (CardsSub.set (cards_destroyAt k (g p))).trans (CardsSub.set ?_)
              rw [State.set_other _ _ hne]
              exact cards_destroyAt _ _
      · split
        · exact CardsSub.set (cards_destroyAt _ _)
        · split
          · exact CardsSub.set (cards_damage _ _)
          · exact CardsSub.refl g

theorem cardsSub_combat (r : Rules) (g : State) (neg : List Pos) (p : PlayerId) (atk : List Nat)
    (blocks : List (Nat × Nat)) : CardsSub g (g.combat r neg p atk blocks) := by
  simp only [State.combat]
  refine CardsSub.trans ?_ (cardsSub_sweep _ _ _)
  have hne : (!p) ≠ p := by cases p <;> decide
  refine (CardsSub.set (cards_mark _ _)).trans (CardsSub.set ?_)
  rw [State.set_other _ _ hne]
  exact fun x hx => cards_mark _ _ x (cards_damage _ _ x hx)

theorem cardsSub_battle (r : Rules) (g : State) (neg : List Pos) (p : PlayerId) (k : Nat) (sl : Slot)
    (t : Option Nat) : CardsSub g (g.battle r neg p k sl t) := by
  unfold State.battle
  split
  · exact cardsSub_combat r g neg p _ _
  · exact cardsSub_duel r g neg p k sl t

theorem cardsSub_resolve (r : Rules) (p : PlayerId) (g : State) {k : Nat} {sl : Slot} (as : List Action)
    (apply : Bool) (neg : List Pos) (tgt : Option Pos) (hk : (g p).field[k]? = some sl) :
    CardsSub g (g.resolve r p k sl as apply neg tgt) := by
  let g1 := g.set p { g p with field := (g p).field.eraseIdx k }
  let g2 := if apply then as.foldl (State.applyAction r (g.srcOf r p sl tgt) (g.negSlots neg)) g1 else g1
  have h01 : CardsSub g g1 := CardsSub.set fun x hx => by
    simp only [PState.mem_cards] at hx ⊢
    rcases hx with h | h | h | ⟨sl', hsl, rfl⟩
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl h))
    · exact .inr (.inr (.inr ⟨sl', (List.eraseIdx_sublist _ _).subset hsl, rfl⟩))
  have h12 : CardsSub g1 g2 := by
    by_cases ha : apply
    · simp only [g2, ha, ite_true]; exact cardsSub_foldl r _ _ as g1
    · simp only [g2, ha]; exact CardsSub.refl g1
  have h02 := h01.trans h12
  have hsl : sl.card ∈ (g p).cards :=
    PState.mem_cards.2 (.inr (.inr (.inr ⟨sl, List.mem_of_getElem? hk, rfl⟩)))
  have hr : g.resolve r p k sl as apply neg tgt = g2.set p { g2 p with grave := (g2 p).grave ++ [sl.card] } := rfl
  rw [hr]
  intro q x hx
  by_cases hq : q = p
  · subst hq
    simp only [State.set_same, PState.mem_cards, List.mem_append, List.mem_singleton] at hx
    rcases hx with h | h | (h | rfl) | h
    · exact h02 q x (PState.mem_cards.2 (.inl h))
    · exact h02 q x (PState.mem_cards.2 (.inr (.inl h)))
    · exact h02 q x (PState.mem_cards.2 (.inr (.inr (.inl h))))
    · exact hsl
    · exact h02 q x (PState.mem_cards.2 (.inr (.inr (.inr h))))
  · rw [State.set_other _ _ hq] at hx
    exact h02 q x hx

theorem cardsSub_step {r : Rules} {g g' : State} : Step r g g' → CardsSub g g'
  | .draw _ p c d hd => CardsSub.set fun x hx => by
      simp only [PState.mem_cards, List.mem_append, List.mem_singleton] at hx
      rw [PState.mem_cards, hd]
      rcases hx with h | (h | rfl) | h | h
      · exact .inl (List.mem_cons_of_mem _ h)
      · exact .inr (.inl h)
      · exact .inl List.mem_cons_self
      · exact .inr (.inr (.inl h))
      · exact .inr (.inr (.inr h))
  | .place _ p c i _ z up hc _ _ _ _ _ => CardsSub.set fun x hx => by
      simp only [PState.mem_cards, List.mem_append, List.mem_singleton] at hx
      rw [PState.mem_cards]
      rcases hx with h | h | h | ⟨sl, h | rfl, rfl⟩
      · exact .inl h
      · exact .inr (.inl (List.mem_of_mem_erase h))
      · exact .inr (.inr (.inl h))
      · exact .inr (.inr (.inr ⟨sl, h, rfl⟩))
      · exact .inr (.inl hc)
  | .resolve _ p k sl as apply neg tgt hk _ => cardsSub_resolve r p g as apply neg tgt hk
  | .attack _ p k sl t neg _ _ _ _ => cardsSub_battle r g neg p k sl t
  | .combat _ p atk blocks neg _ => cardsSub_combat r g neg p atk blocks
  | .mend _ => cardsSub_mend g
  | .settle _ neg => cardsSub_sweep r g neg

/-- 到達できる状態のどのカードも、カードの一覧 `pool` にある -/
def FromPool (pool : List Card) (g : State) : Prop := ∀ q, ∀ x ∈ (g q).cards, x ∈ pool

/-- **一覧のカードだけでデッキを作れば、到達できるどの状態のカードも一覧のカード** -/
theorem Reachable.fromPool {r : Rules} {decks : PlayerId → List Card} {pool : List Card}
    (hpool : ∀ p, ∀ x ∈ decks p, x ∈ pool) {g : State} (hg : Reachable r decks g) : FromPool pool g := by
  induction hg with
  | start =>
    intro q x hx
    simp only [CardGen.start, PState.mem_cards] at hx
    rcases hx with h | h | h | ⟨_, h, _⟩
    · exact hpool q x (List.mem_of_mem_drop h)
    · exact hpool q x (List.mem_of_mem_take h)
    · simp at h
    · simp at h
  | step _ hs ih => exact fun q x hx => ih q x (cardsSub_step hs q x hx)

/-- フィールドのカードも一覧のカード -/
theorem FromPool.field {pool : List Card} {g : State} (h : FromPool pool g) {q : PlayerId} {sl : Slot}
    (hsl : sl ∈ (g q).field) : sl.card ∈ pool :=
  h q _ (PState.mem_cards.2 (.inr (.inr (.inr ⟨sl, hsl, rfl⟩))))

/-! ## ライフの上限 -/

def Action.isHeal : Action → Bool
  | .heal _ => true
  | _ => false

/-- 「回復」の動きを持つ -/
def Card.heals (c : Card) : Bool := c.effects.any fun
  | .activated as => as.any Action.isHeal
  | _ => false

/-- ライフが `L` 以下 -/
def LifeLe (L : Nat) (g : State) : Prop := ∀ q, (g q).life ≤ L

/-- ライフを変えずに各プレイヤーの状態を変える -/
theorem LifeLe.map {L : Nat} {g : State} {f : PlayerId → PState → PState} (h : LifeLe L g)
    (hf : ∀ q s, (f q s).life = s.life) : LifeLe L (g.map f) := by
  intro q; rw [State.map_apply, hf]; exact h q

theorem lifeLe_sweep {L : Nat} (r : Rules) {g : State} (h : LifeLe L g) (neg : List Pos) :
    LifeLe L (g.sweep r neg) := h.map fun _ _ => rfl

theorem lifeLe_mark {L : Nat} {g g' : State} (h : LifeLe L g) (he : ∀ q, (g' q).life = (g q).life) : LifeLe L g' :=
  fun q => (he q) ▸ h q

theorem lifeLe_strike {L : Nat} (r : Rules) {g : State} (h : LifeLe L g) (sel : Selector) (n : Nat) (src : Src)
    (negS : List (PlayerId × Slot)) : LifeLe L (g.strike r sel n src negS) :=
  have h1 : LifeLe L (g.strikeMarks r sel n src) := h.map fun _ _ => rfl
  lifeLe_sweep r h1 _

theorem lifeLe_pumpAll {L : Nat} (r : Rules) {g : State} (h : LifeLe L g) (sel : Selector) (a d : Int) (src : Src)
    (negS : List (PlayerId × Slot)) : LifeLe L (g.pumpAll r sel a d src negS) :=
  have h1 : LifeLe L (g.pumpMarks r sel a d src) := h.map fun _ _ => rfl
  lifeLe_sweep r h1 _

theorem lifeLe_applyAction {L : Nat} (r : Rules) (src : Src) (negS : List (PlayerId × Slot)) {g : State}
    (h : LifeLe L g) (a : Action) (ha : a.isHeal = false) : LifeLe L (g.applyAction r src negS a) := by
  obtain ⟨p, c⟩ := src
  cases a with
  | destroy sel => exact h.map fun _ _ => rfl
  | bounce sel => exact h.map fun _ _ => rfl
  | strike sel n => exact lifeLe_strike r h sel n _ negS
  | pump sel a d => exact lifeLe_pumpAll r h sel a d _ negS
  | counter sel => exact h.map fun _ _ => rfl
  | heal n => simp [Action.isHeal] at ha
  | draw n =>
    intro q
    by_cases hq : q = p
    · subst hq; simpa [State.applyAction, PState.drawN] using h q
    · simp only [State.applyAction, State.set_other _ _ hq]; exact h q
  | damage n =>
    intro q
    by_cases hq : q = !p
    · subst hq; simp only [State.applyAction, State.set_same, PState.damage]; have := h (!p); omega
    · simp only [State.applyAction, State.set_other _ _ hq]; exact h q

theorem lifeLe_foldl {L : Nat} (r : Rules) (p : Src) (negS : List (PlayerId × Slot)) (as : List Action)
    (has : as.any Action.isHeal = false) :
    ∀ {g : State}, LifeLe L g → LifeLe L (as.foldl (State.applyAction r p negS) g) := by
  induction as with
  | nil => exact fun h => h
  | cons a t ih =>
    intro g h
    simp only [List.any_cons, Bool.or_eq_false_iff] at has
    exact ih has.2 (lifeLe_applyAction r p negS h a has.1)

theorem lifeLe_set {L : Nat} {g : State} {p : PlayerId} {s : PState} (h : LifeLe L g) (hs : s.life ≤ (g p).life) :
    LifeLe L (g.set p s) := by
  intro q
  by_cases hq : q = p
  · subst hq; rw [State.set_same]; exact Nat.le_trans hs (h q)
  · rw [State.set_other _ _ hq]; exact h q

theorem life_destroyAt (k : Nat) (s : PState) : (s.destroyAt k).life = s.life := by
  unfold PState.destroyAt; split <;> rfl

theorem lifeLe_duel {L : Nat} (r : Rules) {g : State} (h : LifeLe L g) (neg : List Pos) (p : PlayerId)
    (k : Nat) (sl : Slot) (t : Option Nat) : LifeLe L (g.duel r neg p k sl t) := by
  have dd : ∀ (j n : Nat) (s : PState), ((s.destroyAt j).damage n).life ≤ s.life := by
    intro j n s; simp only [PState.damage, life_destroyAt]; omega
  have dm : ∀ (n : Nat) (s : PState), (s.damage n).life ≤ s.life := by
    intro n s; simp only [PState.damage]; omega
  cases t with
  | none => exact lifeLe_set h (dm _ _)
  | some j =>
    simp only [State.duel]
    split
    · exact h
    · split
      · split
        · exact lifeLe_set h (dd _ _ _)
        · split
          · exact lifeLe_set h (dd _ _ _)
          · split
            · exact h
            · refine lifeLe_set (lifeLe_set h (by rw [life_destroyAt]; exact Nat.le_refl _)) ?_
              simp [life_destroyAt]
      · split
        · exact lifeLe_set h (by rw [life_destroyAt]; exact Nat.le_refl _)
        · split
          · exact lifeLe_set h (dm _ _)
          · exact h

theorem lifeLe_combat {L : Nat} (r : Rules) {g : State} (h : LifeLe L g) (neg : List Pos) (p : PlayerId)
    (atk : List Nat) (blocks : List (Nat × Nat)) : LifeLe L (g.combat r neg p atk blocks) := by
  simp only [State.combat]
  refine lifeLe_sweep r ?_ neg
  refine lifeLe_set (lifeLe_set h (Nat.le_refl _)) ?_
  have hne : (!p) ≠ p := by cases p <;> decide
  rw [State.set_other _ _ hne]
  simp only [PState.damage, PState.mark]
  omega

theorem lifeLe_battle {L : Nat} (r : Rules) {g : State} (h : LifeLe L g) (neg : List Pos) (p : PlayerId)
    (k : Nat) (sl : Slot) (t : Option Nat) : LifeLe L (g.battle r neg p k sl t) := by
  unfold State.battle
  split
  · exact lifeLe_combat r h neg p _ _
  · exact lifeLe_duel r h neg p k sl t

/-- **一覧に「回復」の動きを持つカードがなければ、到達できるどの状態でもライフは初期ライフ以下** -/
theorem Reachable.life_le {r : Rules} {decks : PlayerId → List Card} {pool : List Card}
    (hpool : ∀ p, ∀ x ∈ decks p, x ∈ pool) (hheal : pool.all (!·.heals) = true)
    {g : State} (hg : Reachable r decks g) : LifeLe r.life g := by
  induction hg with
  | start => intro q; simp [CardGen.start]
  | @step g g' hg' hs ih =>
    cases hs with
    | draw p c d hd => exact lifeLe_set ih (Nat.le_refl _)
    | place p c i z up _ _ _ _ _ => exact lifeLe_set ih (Nat.le_refl _)
    | attack p k sl t neg _ _ _ _ => exact lifeLe_battle r ih neg p k sl t
    | combat p atk blocks neg _ => exact lifeLe_combat r ih neg p atk blocks
    | mend => exact ih.map fun _ _ => rfl
    | settle neg => exact lifeLe_sweep r ih neg
    | resolve p k sl as apply neg tgt hk hact =>
      have hcard : sl.card ∈ pool := (hg'.fromPool hpool).field (List.mem_of_getElem? hk)
      have hno : sl.card.heals = false := by
        have := List.all_eq_true.1 hheal _ hcard
        simpa using this
      have has : as.any Action.isHeal = false := by
        unfold Card.heals at hno
        have := List.any_eq_false.1 hno _ hact
        simpa using this
      let g1 := g.set p { g p with field := (g p).field.eraseIdx k }
      have h1 : LifeLe r.life g1 := lifeLe_set ih (Nat.le_refl _)
      have h2 : LifeLe r.life
          (if apply then as.foldl (State.applyAction r (g.srcOf r p sl tgt) (g.negSlots neg)) g1 else g1) := by
        split
        · exact lifeLe_foldl r _ _ as has h1
        · exact h1
      exact lifeLe_set h2 (Nat.le_refl _)

/-! ## カードの一覧によって決まる★ -/

/-- カードの一覧によって決まる★の中身 -/
def gameProps (g : Game) : List ClaimProp :=
  if g.rules.life > 0 && g.cards.all (!·.heals) then [.lifeMax g.rules.life] else []

/-- **カードの一覧によって決まる★は、一覧のカードで作ったどのデッキでも成り立つ** -/
theorem gameProps_sound (g : Game) (decks : PlayerId → List Card) (hpool : ∀ p, ∀ x ∈ decks p, x ∈ g.cards) :
    ∀ c ∈ gameProps g, c.Valid g.rules decks := by
  intro c hc
  unfold gameProps at hc
  split at hc
  · rename_i h
    simp only [List.mem_singleton] at hc; subst hc
    simp only [Bool.and_eq_true] at h
    simp only [ClaimProp.Valid, ClaimProp.atStart]
    intro s hs p
    exact hs.life_le hpool h.2 p
  · simp at hc

/-- 人が読む形の、カードの一覧によって決まる★ -/
def gameClaims (g : Game) : List Claim := (gameProps g).map (·.describe g.rules)

theorem gameClaims_valid (g : Game) (decks : PlayerId → List Card) (hpool : ∀ p, ∀ x ∈ decks p, x ∈ g.cards) :
    ∀ c ∈ gameClaims g, c.prop.Valid g.rules decks := by
  intro c hc
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hc
  rw [ClaimProp.describe_prop]
  exact gameProps_sound g decks hpool p hp

end CardGen
