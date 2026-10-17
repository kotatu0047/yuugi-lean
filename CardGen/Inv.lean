import CardGen.Model

/-!
# どの盤面でも成り立つ盤面の制約

到達できるどの状態でも、次の3つが成り立つ（`Reachable.inv`）。

- 1人あたりのカードの枚数はデッキの枚数のまま
- フィールドのカードは、その種類を置けるゾーンにある
- 「1枚まで」のゾーンのカードは、マスの数を超えない

効果の動き（破壊）はどのカードのどんな範囲の指定でもカードを墓地へ移すだけなので、
カードの効果をどう組み合わせても崩れない（企画書の「第1層」）。
-/

namespace CardGen

theorem length_filter_not_add {α} (p : α → Bool) (l : List α) :
    (l.filter (fun x => !p x)).length + (l.filter p).length = l.length := by
  induction l with
  | nil => rfl
  | cons a t ih => cases h : p a <;> simp [h] <;> omega

/-- 盤面の制約 -/
structure Inv (r : Rules) (g : State) : Prop where
  size : ∀ p, (g p).size = r.deckSize
  zones : ∀ p, ∀ sl ∈ (g p).field,
    ∃ z, r.zones[sl.zone]? = some z ∧ z.role = .plain ∧ z.admits.contains sl.card.type
  cap : ∀ p i z, r.zones[i]? = some z → z.capacity = .one →
    ((g p).field.filter (·.zone == i)).length ≤ z.count

/-! ## カードを取り除くだけの動き -/

/-- どのプレイヤーも、枚数は同じでフィールドのカードは減るだけ -/
def Shrinks (g g' : State) : Prop :=
  ∀ q, (g' q).size = (g q).size ∧ (g' q).field.Sublist (g q).field

theorem Shrinks.refl (g : State) : Shrinks g g := fun _ => ⟨rfl, List.Sublist.refl _⟩

theorem Shrinks.trans {a b c : State} (h1 : Shrinks a b) (h2 : Shrinks b c) : Shrinks a c :=
  fun q => ⟨(h2 q).1.trans (h1 q).1, (h2 q).2.trans (h1 q).2⟩

theorem Inv.shrinks {r : Rules} {g g' : State} (h : Inv r g) (hs : Shrinks g g') : Inv r g' where
  size p := (hs p).1.trans (h.size p)
  zones p sl hm := h.zones p sl ((hs p).2.subset hm)
  cap p i z hz hc := Nat.le_trans ((hs p).2.filter _).length_le (h.cap p i z hz hc)

theorem PState.size_destroy (r : Rules) (sel : Selector) (m : Bool) (s : PState) :
    (s.destroy r sel m).size = s.size := by
  have := length_filter_not_add (fun sl : Slot => r.onFieldZone sl.zone && sel.matches (sl.view m)) s.field
  simp only [PState.destroy, PState.size, List.length_append, List.length_map]
  omega

theorem shrinks_applyAction (r : Rules) (p : PlayerId) (g : State) (a : Action) :
    Shrinks g (g.applyAction r p a) := by
  cases a with
  | destroy sel => exact fun q => ⟨PState.size_destroy .., List.filter_sublist⟩

theorem shrinks_foldl (r : Rules) (p : PlayerId) (as : List Action) (g : State) :
    Shrinks g (as.foldl (State.applyAction r p) g) := by
  induction as generalizing g with
  | nil => exact Shrinks.refl g
  | cons a t ih => exact (shrinks_applyAction r p g a).trans (ih _)

theorem shrinks_resolve (r : Rules) (p : PlayerId) (g : State) {k : Nat} {sl : Slot} (as : List Action)
    (apply : Bool) (hk : (g p).field[k]? = some sl) : Shrinks g (g.resolve r p k sl as apply) := by
  have hlt : k < (g p).field.length := (List.getElem?_eq_some_iff.1 hk).1
  let g1 := g.set p { g p with field := (g p).field.eraseIdx k }
  let g2 := if apply then as.foldl (State.applyAction r p) g1 else g1
  have h12 : Shrinks g1 g2 := by
    by_cases ha : apply
    · simp only [g2, ha, ite_true]; exact shrinks_foldl r p as g1
    · simp only [g2, ha]; exact Shrinks.refl g1
  have hr : g.resolve r p k sl as apply = g2.set p { g2 p with grave := (g2 p).grave ++ [sl.card] } := rfl
  rw [hr]
  intro q
  by_cases hq : q = p
  · subst hq
    have h1 : (g1 q).size + 1 = (g q).size := by
      simp only [g1, State.set_same, PState.size, List.length_eraseIdx, hlt, ite_true]
      omega
    have hs1 : (g1 q).field.Sublist (g q).field := by
      simp only [g1, State.set_same]; exact List.eraseIdx_sublist _ _
    refine ⟨?_, ?_⟩
    · simp only [State.set_same, PState.size, List.length_append, List.length_singleton]
      have := (h12 q).1; simp only [PState.size] at this h1; omega
    · simp only [State.set_same]; exact (h12 q).2.trans hs1
  · have h1 : g1 q = g q := State.set_other _ _ hq
    rw [State.set_other _ _ hq, ← h1]; exact h12 q

/-! ## 動きのたびに制約が保たれる -/

theorem Inv.step {r : Rules} {g g' : State} (h : Inv r g) : Step r g g' → Inv r g'
  | .draw _ p c d hd => h.shrinks fun q => by
      by_cases hq : q = p
      · subst hq
        refine ⟨?_, by simp⟩
        simp [PState.size, hd]
        omega
      · rw [State.set_other _ _ hq]; exact ⟨rfl, List.Sublist.refl _⟩
  | .place _ p c i z up hc hz hrole hadm hcap => by
      have hlen := List.length_erase_of_mem hc
      have hpos := List.length_pos_of_mem hc
      refine ⟨fun q => ?_, fun q sl hm => ?_, fun q j z' hz' hc' => ?_⟩
      · by_cases hq : q = p
        · subst hq
          have := h.size q
          simp only [PState.size] at this
          simp only [State.set_same, PState.size, List.length_append, List.length_singleton, hlen]
          omega
        · simp only [State.set_other _ _ hq]; exact h.size q
      · by_cases hq : q = p
        · subst hq
          simp only [State.set_same, List.mem_append, List.mem_singleton] at hm
          rcases hm with hm | rfl
          · exact h.zones q sl hm
          · exact ⟨z, hz, hrole, hadm⟩
        · simp only [State.set_other _ _ hq] at hm; exact h.zones q sl hm
      · by_cases hq : q = p
        · subst hq
          simp only [State.set_same, List.filter_append, List.length_append]
          by_cases hij : i = j
          · subst hij
            have : z' = z := Option.some.inj (hz'.symm.trans hz)
            subst this
            have := hcap hc'
            simp
            omega
          · have : ((⟨i, c, up⟩ : Slot).zone == j) = false := by simp [hij]
            simp only [List.filter_cons, this, List.filter_nil]
            exact h.cap q j z' hz' hc'
        · simp only [State.set_other _ _ hq]; exact h.cap q j z' hz' hc'
  | .resolve _ p k sl as apply hk _ => h.shrinks (shrinks_resolve r p g as apply hk)

theorem inv_start (r : Rules) (decks : PlayerId → List Card) (hd : ∀ p, (decks p).length = r.deckSize) :
    Inv r (start r decks) where
  size p := by
    simp only [start, PState.size, List.length_drop, List.length_take, List.length_nil, hd p]
    omega
  zones _ _ hm := by simp [start] at hm
  cap _ _ _ _ _ := by simp [start]

/-- **到達できるどの状態でも、盤面の制約が成り立つ** -/
theorem Reachable.inv {r : Rules} {decks : PlayerId → List Card} (hd : ∀ p, (decks p).length = r.deckSize)
    {g : State} (h : Reachable r decks g) : Inv r g := by
  induction h with
  | start => exact inv_start r decks hd
  | step _ hs ih => exact ih.step hs

end CardGen
