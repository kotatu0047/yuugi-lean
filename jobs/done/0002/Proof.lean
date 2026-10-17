-- カードの一覧に闇属性の罠はない。動きはカードを移すだけなので、盤面のカードはどれもデッキ（＝一覧）から来ている

/-- 1人分の状態にあるカード -/
def cardsOf (s : PState) : List Card := s.deck ++ s.hand ++ s.grave ++ s.field.map (·.card)

theorem mem_cardsOf {s : PState} {x : Card} :
    x ∈ cardsOf s ↔ x ∈ s.deck ∨ x ∈ s.hand ∨ x ∈ s.grave ∨ ∃ sl ∈ s.field, sl.card = x := by
  simp [cardsOf]

/-- 動きの後のどのプレイヤーのカードも、動きの前にそのプレイヤーのところにあった -/
def Sub (g g' : State) : Prop := ∀ q, ∀ x ∈ cardsOf (g' q), x ∈ cardsOf (g q)

theorem Sub.refl (g : State) : Sub g g := fun _ _ h => h

theorem Sub.trans {a b c : State} (h1 : Sub a b) (h2 : Sub b c) : Sub a c :=
  fun q x hx => h1 q x (h2 q x hx)

theorem sub_destroy (r : Rules) (sel : Selector) (m : Bool) (s : PState) :
    ∀ x ∈ cardsOf (s.destroy r sel m), x ∈ cardsOf s := by
  intro x hx
  simp only [mem_cardsOf, PState.destroy, List.mem_append, List.mem_map, List.mem_filter] at hx ⊢
  rcases hx with h | h | (h | ⟨sl, ⟨hsl, _⟩, rfl⟩) | ⟨sl, ⟨hsl, _⟩, rfl⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl h))
  · exact .inr (.inr (.inr ⟨sl, hsl, rfl⟩))
  · exact .inr (.inr (.inr ⟨sl, hsl, rfl⟩))

theorem sub_foldl (r : Rules) (p : PlayerId) (as : List Action) (g : State) :
    Sub g (as.foldl (State.applyAction r p) g) := by
  induction as generalizing g with
  | nil => exact Sub.refl g
  | cons a t ih =>
    refine Sub.trans ?_ (ih _)
    cases a with
    | destroy sel => exact fun q => sub_destroy r sel (q == p) (g q)

theorem sub_step {r : Rules} {g g' : State} : Step r g g' → Sub g g'
  | .draw _ p c d hd => fun q x hx => by
      by_cases hq : q = p
      · subst hq
        simp only [State.set_same, mem_cardsOf, List.mem_append, List.mem_singleton] at hx
        rw [mem_cardsOf, hd]
        rcases hx with h | (h | rfl) | h | h
        · exact .inl (List.mem_cons_of_mem _ h)
        · exact .inr (.inl h)
        · exact .inl (List.mem_cons_self ..)
        · exact .inr (.inr (.inl h))
        · exact .inr (.inr (.inr h))
      · rwa [State.set_other _ _ hq] at hx
  | .place _ p c i z up hc _ _ _ _ => fun q x hx => by
      by_cases hq : q = p
      · subst hq
        simp only [State.set_same, mem_cardsOf, List.mem_append, List.mem_singleton] at hx
        rw [mem_cardsOf]
        rcases hx with h | h | h | ⟨sl, h | rfl, rfl⟩
        · exact .inl h
        · exact .inr (.inl (List.mem_of_mem_erase h))
        · exact .inr (.inr (.inl h))
        · exact .inr (.inr (.inr ⟨sl, h, rfl⟩))
        · exact .inr (.inl hc)
      · rwa [State.set_other _ _ hq] at hx
  | .resolve _ p k sl as apply hk _ => by
      let g1 := g.set p { g p with field := (g p).field.eraseIdx k }
      let g2 := if apply then as.foldl (State.applyAction r p) g1 else g1
      have h01 : Sub g g1 := fun q x hx => by
        by_cases hq : q = p
        · subst hq
          simp only [g1, State.set_same, mem_cardsOf] at hx
          rw [mem_cardsOf]
          rcases hx with h | h | h | ⟨sl', hsl, rfl⟩
          · exact .inl h
          · exact .inr (.inl h)
          · exact .inr (.inr (.inl h))
          · exact .inr (.inr (.inr ⟨sl', (List.eraseIdx_sublist _ _).subset hsl, rfl⟩))
        · simp only [g1, State.set_other _ _ hq] at hx; exact hx
      have h12 : Sub g1 g2 := by
        by_cases ha : apply
        · simp only [g2, ha, ite_true]; exact sub_foldl r p as g1
        · simp only [g2, ha]; exact Sub.refl g1
      have h02 := h01.trans h12
      have hsl : sl.card ∈ cardsOf (g p) :=
        mem_cardsOf.2 (.inr (.inr (.inr ⟨sl, List.mem_of_getElem? hk, rfl⟩)))
      intro q x hx
      have hr : g.resolve r p k sl as apply = g2.set p { g2 p with grave := (g2 p).grave ++ [sl.card] } := rfl
      rw [hr] at hx
      by_cases hq : q = p
      · subst hq
        simp only [State.set_same, mem_cardsOf, List.mem_append, List.mem_singleton] at hx
        rcases hx with h | h | (h | rfl) | h
        · exact h02 q x (mem_cardsOf.2 (.inl h))
        · exact h02 q x (mem_cardsOf.2 (.inr (.inl h)))
        · exact h02 q x (mem_cardsOf.2 (.inr (.inr (.inl h))))
        · exact hsl
        · exact h02 q x (mem_cardsOf.2 (.inr (.inr (.inr h))))
      · rw [State.set_other _ _ hq] at hx
        exact h02 q x hx

/-- 一覧のカードだけでデッキを作れば、到達できるどの状態のカードも一覧のカード -/
theorem cards_in_pool {decks : PlayerId → List Card} (hpool : ∀ p, ∀ x ∈ decks p, x ∈ cards)
    {g : State} (hg : Reachable rules decks g) : ∀ q, ∀ x ∈ cardsOf (g q), x ∈ cards := by
  induction hg with
  | start =>
    intro q x hx
    simp only [start, mem_cardsOf, List.not_mem_nil, false_or] at hx
    rcases hx with h | h | ⟨_, h, _⟩
    · exact hpool q x (List.mem_of_mem_drop h)
    · exact hpool q x (List.mem_of_mem_take h)
    · exact h.elim
  | step _ hs ih => exact fun q x hx => ih q x (sub_step hs q x hx)

theorem job_proof : JobStatement := by
  intro decks _ hpool g hg
  have hnone : ∀ c ∈ cards, claim.matches c = false := by decide
  have hzero : ∀ q, countWhere rules claim.matches (g q) = 0 := by
    intro q
    unfold countWhere
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro sl hsl h
    have hc := cards_in_pool hpool hg q sl.card (mem_cardsOf.2 (.inr (.inr (.inr ⟨sl, hsl, rfl⟩))))
    simp [hnone _ hc] at h
  show countWhere rules claim.matches (g true) + countWhere rules claim.matches (g false) ≤ 0
  simp [hzero]
