import CardGen.Model

/-!
# どの盤面でも成り立つ盤面の制約

到達できるどの状態でも、次の3つが成り立つ（`Reachable.inv`）。

- 1人あたりのカードの枚数はデッキの枚数のまま
- フィールドのカードは、その種類を置けるゾーンのマスにある
- 「1枚まで」のゾーンの同じマスに、2枚のカードはない（そのため、ゾーンのカードはマスの数を超えない：`Inv.cap`）
- デッキの枚数は、開始時の枚数（デッキの枚数 − 初期手札）を超えない（デッキに戻す動きはない）

効果の動き（破壊・手札に戻す・ドロー・ダメージ・回復）と戦闘は、どのカードのどんな範囲の指定でも
カードを移すかライフを変えるだけなので、カードの効果をどう組み合わせても崩れない（企画書の「第1層」）。
-/

namespace CardGen

theorem length_filter_not_add {α} (p : α → Bool) (l : List α) :
    (l.filter (fun x => !p x)).length + (l.filter p).length = l.length := by
  induction l with
  | nil => rfl
  | cons a t ih => cases h : p a <;> simp [h] <;> omega

theorem length_filter_eq_le_one : ∀ (n : Nat) (l : List Nat), l.Nodup → (l.filter (· == n)).length ≤ 1
  | _, [], _ => by simp
  | n, a :: t, hn => by
    rw [List.nodup_cons] at hn
    by_cases ha : a = n
    · subst ha
      have : t.filter (· == a) = [] := List.filter_eq_nil_iff.2 fun x hx => by
        simp only [beq_iff_eq]; intro h; subst h; exact hn.1 hx
      simp [this]
    · have := length_filter_eq_le_one n t hn.2
      simp [ha, this]

/-- 鳩の巣原理：`n` 未満の数を重複なく並べると、`n` 個以下 -/
theorem length_le_of_nodup_lt : ∀ (n : Nat) (l : List Nat), l.Nodup → (∀ x ∈ l, x < n) → l.length ≤ n
  | 0, [], _, _ => Nat.le_refl _
  | 0, x :: _, _, h => absurd (h x (List.mem_cons_self ..)) (Nat.not_lt_zero _)
  | n + 1, l, hn, h => by
    have ih := length_le_of_nodup_lt n (l.filter (fun x => !(x == n))) (hn.filter _) (by
      intro x hx
      simp only [List.mem_filter, Bool.not_eq_true', beq_eq_false_iff_ne] at hx
      have := h x hx.1; omega)
    have hc := length_filter_eq_le_one n l hn
    have hs := length_filter_not_add (· == n) l
    omega

/-- `i` 番目のゾーンが「1枚まで」のゾーンか -/
def Rules.capOne (r : Rules) (i : Nat) : Bool :=
  match r.zones[i]? with
  | some z => z.capacity == .one
  | none => false

/-- 2枚のカードが、「1枚まで」のゾーンの同じマスにある -/
def Rules.clash (r : Rules) (a b : Slot) : Prop := a.zone = b.zone ∧ a.cell = b.cell ∧ r.capOne a.zone = true

/-- 盤面の制約 -/
structure Inv (r : Rules) (g : State) : Prop where
  size : ∀ p, (g p).size = r.deckSize
  zones : ∀ p, ∀ sl ∈ (g p).field,
    ∃ z, r.zones[sl.zone]? = some z ∧ z.role = .plain ∧ z.admits.contains sl.card.type ∧ sl.cell < z.count
  apart : ∀ p, (g p).field.Pairwise (fun a b => ¬r.clash a b)
  deck : ∀ p, (g p).deck.length ≤ r.deckSize - r.handSize

/-- 「1枚まで」のゾーンのカードは、マスの数を超えない -/
theorem Inv.cap {r : Rules} {g : State} (h : Inv r g) (p : PlayerId) (i : Nat) (z : Zone)
    (hz : r.zones[i]? = some z) (hc : z.capacity = .one) :
    ((g p).field.filter (·.zone == i)).length ≤ z.count := by
  have hone : r.capOne i = true := by simp [Rules.capOne, hz, hc]
  have hnd : (((g p).field.filter (·.zone == i)).map (·.cell)).Nodup := by
    rw [List.Nodup, List.pairwise_map]
    refine ((h.apart p).filter _).imp_of_mem fun ha hb hab heq => hab ?_
    simp only [List.mem_filter, beq_iff_eq] at ha hb
    exact ⟨ha.2.trans hb.2.symm, heq, ha.2 ▸ hone⟩
  have := length_le_of_nodup_lt z.count _ hnd (by
    intro x hx
    simp only [List.mem_map, List.mem_filter, beq_iff_eq] at hx
    obtain ⟨sl, ⟨hm, hzi⟩, rfl⟩ := hx
    obtain ⟨z', hz', -, -, hlt⟩ := h.zones p sl hm
    rw [hzi, hz] at hz'
    cases hz'
    exact hlt)
  simpa using this

/-! ## カードを取り除くだけの動き -/

/-- どのプレイヤーも、枚数は同じでフィールドのカードとデッキは減るだけ -/
def Shrinks (g g' : State) : Prop :=
  ∀ q, (g' q).size = (g q).size ∧ (g' q).field.Sublist (g q).field ∧ (g' q).deck.length ≤ (g q).deck.length

theorem Shrinks.refl (g : State) : Shrinks g g := fun _ => ⟨rfl, List.Sublist.refl _, Nat.le_refl _⟩

theorem Shrinks.trans {a b c : State} (h1 : Shrinks a b) (h2 : Shrinks b c) : Shrinks a c :=
  fun q => ⟨(h2 q).1.trans (h1 q).1, (h2 q).2.1.trans (h1 q).2.1, Nat.le_trans (h2 q).2.2 (h1 q).2.2⟩

theorem Inv.shrinks {r : Rules} {g g' : State} (h : Inv r g) (hs : Shrinks g g') : Inv r g' where
  size p := (hs p).1.trans (h.size p)
  zones p sl hm := h.zones p sl ((hs p).2.1.subset hm)
  apart p := (h.apart p).sublist (hs p).2.1
  deck p := Nat.le_trans (hs p).2.2 (h.deck p)

theorem PState.size_destroy (r : Rules) (sel : Selector) (q : PlayerId) (src : Src) (s : PState) :
    (s.destroy r sel q src).size = s.size := by
  have := length_filter_not_add (fun sl : Slot => r.onFieldZone sl.zone && sel.matches (sl.view r q src)) s.field
  simp only [PState.destroy, PState.size, List.length_append, List.length_map]
  omega

theorem PState.size_bounce (r : Rules) (sel : Selector) (q : PlayerId) (src : Src) (s : PState) :
    (s.bounce r sel q src).size = s.size := by
  have := length_filter_not_add (fun sl : Slot => r.onFieldZone sl.zone && sel.matches (sl.view r q src)) s.field
  simp only [PState.bounce, PState.size, List.length_append, List.length_map]
  omega

theorem PState.size_drawN (n : Nat) (s : PState) : (s.drawN n).size = s.size := by
  simp only [PState.drawN, PState.size, List.length_append, List.length_drop, List.length_take]
  omega

/-- 1人分の状態が、枚数は同じでフィールドのカードとデッキは減るだけ -/
def PShrinks (s s' : PState) : Prop :=
  s'.size = s.size ∧ s'.field.Sublist s.field ∧ s'.deck.length ≤ s.deck.length

theorem PShrinks.refl (s : PState) : PShrinks s s := ⟨rfl, List.Sublist.refl _, Nat.le_refl _⟩

theorem PShrinks.trans {a b c : PState} (h1 : PShrinks a b) (h2 : PShrinks b c) : PShrinks a c :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, Nat.le_trans h2.2.2 h1.2.2⟩

theorem pshrinks_damage (n : Nat) (s : PState) : PShrinks s (s.damage n) := PShrinks.refl s

theorem pshrinks_destroyAt (k : Nat) (s : PState) : PShrinks s (s.destroyAt k) := by
  unfold PState.destroyAt
  split
  · rename_i sl hk
    have hlt : k < s.field.length := (List.getElem?_eq_some_iff.1 hk).1
    refine ⟨?_, List.eraseIdx_sublist _ _, Nat.le_refl _⟩
    simp only [PState.size, List.length_append, List.length_eraseIdx, hlt, ite_true, List.length_singleton]
    omega
  · exact PShrinks.refl s

/-- 1人分だけ変える -/
theorem Shrinks.set {g : State} {p : PlayerId} {s : PState} (h : PShrinks (g p) s) : Shrinks g (g.set p s) := by
  intro q
  by_cases hq : q = p
  · subst hq; rw [State.set_same]; exact h
  · rw [State.set_other _ _ hq]; exact Shrinks.refl g q

theorem shrinks_battle (r : Rules) (g : State) (neg : List Pos) (p : PlayerId) (k : Nat) (sl : Slot)
    (t : Option Nat) : Shrinks g (g.battle r neg p k sl t) := by
  cases t with
  | none => exact Shrinks.set (pshrinks_damage _ _)
  | some j =>
    simp only [State.battle]
    split
    · exact Shrinks.refl g
    · split
      · split
        · exact Shrinks.set ((pshrinks_destroyAt _ _).trans (pshrinks_damage _ _))
        · split
          · exact Shrinks.set ((pshrinks_destroyAt _ _).trans (pshrinks_damage _ _))
          · split
            · exact Shrinks.refl g
            · have hne : (!p) ≠ p := by cases p <;> decide
              refine (Shrinks.set (pshrinks_destroyAt k (g p))).trans (Shrinks.set ?_)
              rw [State.set_other _ _ hne]
              exact pshrinks_destroyAt _ _
      · split
        · exact Shrinks.set (pshrinks_destroyAt _ _)
        · split
          · exact Shrinks.set (pshrinks_damage _ _)
          · exact Shrinks.refl g

theorem shrinks_applyAction (r : Rules) (src : Src) (g : State) (a : Action) :
    Shrinks g (g.applyAction r src a) := by
  cases a with
  | destroy sel => exact fun q => ⟨PState.size_destroy .., List.filter_sublist, Nat.le_refl _⟩
  | bounce sel => exact fun q => ⟨PState.size_bounce .., List.filter_sublist, Nat.le_refl _⟩
  | draw n =>
    intro q
    by_cases hq : q = src.p
    · subst hq
      simp only [State.applyAction, State.set_same]
      exact ⟨PState.size_drawN .., List.Sublist.refl _, by simp [PState.drawN]⟩
    · have h := State.set_other g ((g src.p).drawN n) hq
      simp only [State.applyAction]
      rw [h]
      exact Shrinks.refl g q
  | damage n => exact Shrinks.set (pshrinks_damage _ _)
  | heal n => exact Shrinks.set (PShrinks.refl _)

theorem shrinks_foldl (r : Rules) (src : Src) (as : List Action) (g : State) :
    Shrinks g (as.foldl (State.applyAction r src) g) := by
  induction as generalizing g with
  | nil => exact Shrinks.refl g
  | cons a t ih => exact (shrinks_applyAction r src g a).trans (ih _)

theorem shrinks_resolve (r : Rules) (p : PlayerId) (g : State) {k : Nat} {sl : Slot} (as : List Action)
    (apply : Bool) (hk : (g p).field[k]? = some sl) : Shrinks g (g.resolve r p k sl as apply) := by
  have hlt : k < (g p).field.length := (List.getElem?_eq_some_iff.1 hk).1
  let g1 := g.set p { g p with field := (g p).field.eraseIdx k }
  let g2 := if apply then as.foldl (State.applyAction r ⟨p, r.cellOf p sl⟩) g1 else g1
  have h12 : Shrinks g1 g2 := by
    by_cases ha : apply
    · simp only [g2, ha, ite_true]; exact shrinks_foldl r _ as g1
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
    refine ⟨?_, ?_, ?_⟩
    · simp only [State.set_same, PState.size, List.length_append, List.length_singleton]
      have := (h12 q).1; simp only [PState.size] at this h1; omega
    · simp only [State.set_same]; exact (h12 q).2.1.trans hs1
    · have := (h12 q).2.2; simp only [g1, State.set_same] at this; simpa using this
  · have h1 : g1 q = g q := State.set_other _ _ hq
    rw [State.set_other _ _ hq, ← h1]; exact h12 q

/-! ## 動きのたびに制約が保たれる -/

theorem Inv.step {r : Rules} {g g' : State} (h : Inv r g) : Step r g g' → Inv r g'
  | .draw _ p c d hd => h.shrinks fun q => by
      by_cases hq : q = p
      · subst hq
        refine ⟨?_, by simp, by simp [hd]⟩
        simp [PState.size, hd]
        omega
      · rw [State.set_other _ _ hq]; exact Shrinks.refl g q
  | .place _ p c i j z up hc hz hrole hadm hj hfree => by
      have hlen := List.length_erase_of_mem hc
      have hpos := List.length_pos_of_mem hc
      refine ⟨fun q => ?_, fun q sl hm => ?_, fun q => ?_, fun q => ?_⟩
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
          · exact ⟨z, hz, hrole, hadm, hj⟩
        · simp only [State.set_other _ _ hq] at hm; exact h.zones q sl hm
      · by_cases hq : q = p
        · subst hq
          simp only [State.set_same]
          refine List.pairwise_append.2 ⟨h.apart q, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
          rw [List.mem_singleton] at hb
          subst hb
          rintro ⟨hzi, hcj, hone⟩
          simp only at hzi hcj
          rw [hzi] at hone
          simp only [Rules.capOne, hz, beq_iff_eq] at hone
          exact hfree hone a ha ⟨hzi, hcj⟩
        · simp only [State.set_other _ _ hq]; exact h.apart q
      · by_cases hq : q = p
        · subst hq; simpa using h.deck q
        · simp only [State.set_other _ _ hq]; exact h.deck q
  | .resolve _ p k sl as apply hk _ => h.shrinks (shrinks_resolve r p g as apply hk)
  | .attack _ p k sl t neg _ _ _ _ => h.shrinks (shrinks_battle r g neg p k sl t)

theorem inv_start (r : Rules) (decks : PlayerId → List Card) (hd : ∀ p, (decks p).length = r.deckSize) :
    Inv r (start r decks) where
  size p := by
    simp only [start, PState.size, List.length_drop, List.length_take, List.length_nil, hd p]
    omega
  zones _ _ hm := by simp [start] at hm
  apart _ := by simp [start]
  deck p := by simp [start, hd p]

/-- **到達できるどの状態でも、盤面の制約が成り立つ** -/
theorem Reachable.inv {r : Rules} {decks : PlayerId → List Card} (hd : ∀ p, (decks p).length = r.deckSize)
    {g : State} (h : Reachable r decks g) : Inv r g := by
  induction h with
  | start => exact inv_start r decks hd
  | step _ hs ih => exact ih.step hs

end CardGen
