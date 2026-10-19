import CardGen.Model

/-!
# どの盤面でも成り立つ盤面の制約

到達できるどの状態でも、次の3つが成り立つ（`Reachable.inv`）。

- 1人あたりのカードの枚数はデッキの枚数のまま
- フィールドのカードは、その種類を置けるゾーンのマスにある
- 「1枚まで」のゾーンの同じマスに、2枚のカードはない（そのため、ゾーンのカードはマスの数を超えない：`Inv.cap`）
- デッキの枚数は、開始時の枚数（デッキの枚数 − 初期手札）を超えない（デッキに戻す動きはない）

効果の動き（破壊・手札に戻す・ドロー・ダメージ・回復・カードへのダメージ）と戦闘は、どのカードのどんな範囲の指定でも
カードを移すか、ライフやカードの受けたダメージを変えるだけなので、カードの効果をどう組み合わせても崩れない（企画書の「第1層」）。
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

/-! ## カードを取り除くか、ダメージを変えるだけの動き -/

/-- どのプレイヤーも、枚数は同じで、フィールドのカード（ダメージを除く）とデッキは減るだけ -/
def Shrinks (g g' : State) : Prop :=
  ∀ q, (g' q).size = (g q).size ∧ ((g' q).field.map Slot.base).Sublist ((g q).field.map Slot.base) ∧
    (g' q).deck.length ≤ (g q).deck.length

theorem Shrinks.refl (g : State) : Shrinks g g := fun _ => ⟨rfl, List.Sublist.refl _, Nat.le_refl _⟩

theorem Shrinks.trans {a b c : State} (h1 : Shrinks a b) (h2 : Shrinks b c) : Shrinks a c :=
  fun q => ⟨(h2 q).1.trans (h1 q).1, (h2 q).2.1.trans (h1 q).2.1, Nat.le_trans (h2 q).2.2 (h1 q).2.2⟩

/-- 「1枚まで」のゾーンの同じマスにあるかは、ダメージによらない -/
theorem Rules.clash_base (r : Rules) (a b : Slot) : r.clash a.base b.base ↔ r.clash a b := Iff.rfl

theorem Inv.shrinks {r : Rules} {g g' : State} (h : Inv r g) (hs : Shrinks g g') : Inv r g' where
  size p := (hs p).1.trans (h.size p)
  zones p sl hm := by
    have : sl.base ∈ (g p).field.map Slot.base := (hs p).2.1.subset (List.mem_map_of_mem hm)
    obtain ⟨sl0, h0, he⟩ := List.mem_map.1 this
    obtain ⟨z, hz, hr, ha, hc⟩ := h.zones p sl0 h0
    have e1 : sl0.zone = sl.zone := by rw [← Slot.base_zone sl0, he, Slot.base_zone]
    have e2 : sl0.cell = sl.cell := by rw [← Slot.base_cell sl0, he, Slot.base_cell]
    have e3 : sl0.card = sl.card := by rw [← Slot.base_card sl0, he, Slot.base_card]
    exact ⟨z, e1 ▸ hz, hr, e3 ▸ ha, e2 ▸ hc⟩
  apart p := by
    have h1 : ((g p).field.map Slot.base).Pairwise (fun a b => ¬r.clash a b) :=
      List.pairwise_map.2 ((h.apart p).imp fun hab => by rwa [Rules.clash_base])
    have h2 := List.pairwise_map.1 (h1.sublist (hs p).2.1)
    exact h2.imp fun hab => by rwa [Rules.clash_base] at hab
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

theorem PState.size_counter (r : Rules) (sel : Selector) (q : PlayerId) (src : Src) (s : PState) :
    (s.counter r sel q src).size = s.size := by
  have := length_filter_not_add (fun sl : Slot => !r.onFieldZone sl.zone && sel.matches (sl.view r q src)) s.field
  simp only [PState.counter, PState.size, List.length_append, List.length_map]
  omega

theorem PState.size_drawN (n : Nat) (s : PState) : (s.drawN n).size = s.size := by
  simp only [PState.drawN, PState.size, List.length_append, List.length_drop, List.length_take]
  omega

/-- 1人分の状態が、枚数は同じで、フィールドのカード（ダメージを除く）とデッキは減るだけ -/
def PShrinks (s s' : PState) : Prop :=
  s'.size = s.size ∧ (s'.field.map Slot.base).Sublist (s.field.map Slot.base) ∧ s'.deck.length ≤ s.deck.length

theorem PShrinks.refl (s : PState) : PShrinks s s := ⟨rfl, List.Sublist.refl _, Nat.le_refl _⟩

theorem PShrinks.trans {a b c : PState} (h1 : PShrinks a b) (h2 : PShrinks b c) : PShrinks a c :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, Nat.le_trans h2.2.2 h1.2.2⟩

/-- フィールドが元のフィールドの一部になるだけ -/
theorem PShrinks.of_sublist {s s' : PState} (h1 : s'.size = s.size) (h2 : s'.field.Sublist s.field)
    (h3 : s'.deck.length ≤ s.deck.length) : PShrinks s s' := ⟨h1, h2.map _, h3⟩

theorem pshrinks_damage (n : Nat) (s : PState) : PShrinks s (s.damage n) := PShrinks.refl s

theorem pshrinks_destroyAt (k : Nat) (s : PState) : PShrinks s (s.destroyAt k) := by
  unfold PState.destroyAt
  split
  · rename_i sl hk
    have hlt : k < s.field.length := (List.getElem?_eq_some_iff.1 hk).1
    refine PShrinks.of_sublist ?_ (List.eraseIdx_sublist _ _) (Nat.le_refl _)
    simp only [PState.size, List.length_append, List.length_eraseIdx, hlt, ite_true, List.length_singleton]
    omega
  · exact PShrinks.refl s

theorem PState.map_base_mark (d : Nat → Nat) (s : PState) :
    (s.mark d).field.map Slot.base = s.field.map Slot.base := by
  apply List.ext_getElem
  · simp [PState.mark]
  · intro i h1 h2
    simp [PState.mark, Slot.base]

theorem pshrinks_mark (d : Nat → Nat) (s : PState) : PShrinks s (s.mark d) := by
  refine ⟨?_, by rw [PState.map_base_mark]; exact List.Sublist.refl _, Nat.le_refl _⟩
  simp [PState.size, PState.mark]

theorem PState.map_base_pump (d : Nat → Int × Int) (s : PState) :
    (s.pump d).field.map Slot.base = s.field.map Slot.base := by
  apply List.ext_getElem
  · simp [PState.pump]
  · intro i h1 h2
    simp [PState.pump, Slot.base]

theorem pshrinks_pump (d : Nat → Int × Int) (s : PState) : PShrinks s (s.pump d) := by
  refine ⟨?_, by rw [PState.map_base_pump]; exact List.Sublist.refl _, Nat.le_refl _⟩
  simp [PState.size, PState.pump]

theorem pshrinks_sweep (dead : Nat → Slot → Bool) (s : PState) : PShrinks s (s.sweep dead) := by
  refine PShrinks.of_sublist ?_ ?_ (Nat.le_refl _)
  · have := length_filter_not_add (fun x : Slot × Nat => dead x.2 x.1) s.field.zipIdx
    simp only [PState.sweep, PState.size, List.length_append, List.length_map, List.length_zipIdx] at this ⊢
    omega
  · have := (List.filter_sublist (p := fun x : Slot × Nat => !dead x.2 x.1) (l := s.field.zipIdx)).map Prod.fst
    rwa [List.zipIdx_map_fst] at this

theorem pshrinks_mend (s : PState) : PShrinks s { s with field := s.field.map Slot.base } := by
  refine ⟨by simp [PState.size], ?_, Nat.le_refl _⟩
  simp only [List.map_map]
  exact List.Sublist.refl _

/-- 1人分だけ変える -/
theorem Shrinks.set {g : State} {p : PlayerId} {s : PState} (h : PShrinks (g p) s) : Shrinks g (g.set p s) := by
  intro q
  by_cases hq : q = p
  · subst hq; rw [State.set_same]; exact h
  · rw [State.set_other _ _ hq]; exact Shrinks.refl g q

/-- 全員を変える -/
theorem Shrinks.all {g g' : State} (h : ∀ q, PShrinks (g q) (g' q)) : Shrinks g g' := h

/-- 各プレイヤーの状態を変える -/
theorem Shrinks.map {g : State} {f : PlayerId → PState → PState} (h : ∀ q, PShrinks (g q) (f q (g q))) :
    Shrinks g (g.map f) := by
  intro q; rw [State.map_apply]; exact h q

theorem shrinks_sweep (r : Rules) (g : State) (neg : List Pos) : Shrinks g (g.sweep r neg) :=
  Shrinks.map fun q => pshrinks_sweep _ (g q)

theorem shrinks_mend (g : State) : Shrinks g g.mend := Shrinks.map fun q => pshrinks_mend (g q)

theorem shrinks_duel (r : Rules) (g : State) (neg : List Pos) (p : PlayerId) (k : Nat) (sl : Slot)
    (t : Option Nat) : Shrinks g (g.duel r neg p k sl t) := by
  cases t with
  | none => exact Shrinks.set (pshrinks_damage _ _)
  | some j =>
    simp only [State.duel]
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

theorem shrinks_combat (r : Rules) (g : State) (neg : List Pos) (p : PlayerId) (atk : List Nat)
    (blocks : List (Nat × Nat)) : Shrinks g (g.combat r neg p atk blocks) := by
  simp only [State.combat]
  refine Shrinks.trans ?_ (shrinks_sweep _ _ _)
  have hne : (!p) ≠ p := by cases p <;> decide
  refine (Shrinks.set (pshrinks_mark _ _)).trans (Shrinks.set ?_)
  rw [State.set_other _ _ hne]
  exact (pshrinks_mark _ _).trans (pshrinks_damage _ _)

theorem shrinks_battle (r : Rules) (g : State) (neg : List Pos) (p : PlayerId) (k : Nat) (sl : Slot)
    (t : Option Nat) : Shrinks g (g.battle r neg p k sl t) := by
  unfold State.battle
  split
  · exact shrinks_combat r g neg p _ _
  · exact shrinks_duel r g neg p k sl t

theorem shrinks_strike (r : Rules) (sel : Selector) (n : Nat) (src : Src) (negS : List (PlayerId × Slot))
    (g : State) : Shrinks g (g.strike r sel n src negS) :=
  have h : Shrinks g (g.strikeMarks r sel n src) := Shrinks.map fun q => pshrinks_mark _ (g q)
  h.trans (shrinks_sweep _ _ _)

theorem shrinks_pumpAll (r : Rules) (sel : Selector) (a d : Int) (src : Src) (negS : List (PlayerId × Slot))
    (g : State) : Shrinks g (g.pumpAll r sel a d src negS) :=
  have h : Shrinks g (g.pumpMarks r sel a d src) := Shrinks.map fun q => pshrinks_pump _ (g q)
  h.trans (shrinks_sweep _ _ _)

theorem shrinks_applyAction (r : Rules) (src : Src) (negS : List (PlayerId × Slot)) (g : State) (a : Action) :
    Shrinks g (g.applyAction r src negS a) := by
  cases a with
  | destroy sel =>
    exact Shrinks.map fun q => PShrinks.of_sublist (PState.size_destroy ..) List.filter_sublist (Nat.le_refl _)
  | bounce sel =>
    exact Shrinks.map fun q => PShrinks.of_sublist (PState.size_bounce ..) List.filter_sublist (Nat.le_refl _)
  | draw n =>
    intro q
    by_cases hq : q = src.p
    · subst hq
      simp only [State.applyAction, State.set_same]
      exact PShrinks.of_sublist (PState.size_drawN ..) (List.Sublist.refl _) (by simp [PState.drawN])
    · have h := State.set_other g ((g src.p).drawN n) hq
      simp only [State.applyAction]
      rw [h]
      exact Shrinks.refl g q
  | damage n => exact Shrinks.set (pshrinks_damage _ _)
  | heal n => exact Shrinks.set (PShrinks.refl _)
  | strike sel n => exact shrinks_strike r sel n src negS g
  | pump sel a d => exact shrinks_pumpAll r sel a d src negS g
  | counter sel =>
    exact Shrinks.map fun q => PShrinks.of_sublist (PState.size_counter ..) List.filter_sublist (Nat.le_refl _)

theorem shrinks_foldl (r : Rules) (src : Src) (negS : List (PlayerId × Slot)) (as : List Action) (g : State) :
    Shrinks g (as.foldl (State.applyAction r src negS) g) := by
  induction as generalizing g with
  | nil => exact Shrinks.refl g
  | cons a t ih => exact (shrinks_applyAction r src negS g a).trans (ih _)

theorem shrinks_resolve (r : Rules) (p : PlayerId) (g : State) {k : Nat} {sl : Slot} (as : List Action)
    (apply : Bool) (neg : List Pos) (tgt : Option Pos) (hk : (g p).field[k]? = some sl) :
    Shrinks g (g.resolve r p k sl as apply neg tgt) := by
  have hlt : k < (g p).field.length := (List.getElem?_eq_some_iff.1 hk).1
  let g1 := g.set p { g p with field := (g p).field.eraseIdx k }
  let g2 := if apply then as.foldl (State.applyAction r (g.srcOf r p sl tgt) (g.negSlots neg)) g1 else g1
  have h12 : Shrinks g1 g2 := by
    by_cases ha : apply
    · simp only [g2, ha, ite_true]; exact shrinks_foldl r _ _ as g1
    · simp only [g2, ha]; exact Shrinks.refl g1
  have hr : g.resolve r p k sl as apply neg tgt = g2.set p { g2 p with grave := (g2 p).grave ++ [sl.card] } := rfl
  rw [hr]
  intro q
  by_cases hq : q = p
  · subst hq
    have h1 : (g1 q).size + 1 = (g q).size := by
      simp only [g1, State.set_same, PState.size, List.length_eraseIdx, hlt, ite_true]
      omega
    have hs1 : ((g1 q).field.map Slot.base).Sublist ((g q).field.map Slot.base) := by
      simp only [g1, State.set_same]; exact (List.eraseIdx_sublist _ _).map _
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
        refine PShrinks.of_sublist ?_ (by simp) (by simp [hd])
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
  | .resolve _ p k sl as apply neg tgt hk _ => h.shrinks (shrinks_resolve r p g as apply neg tgt hk)
  | .attack _ p k sl t neg _ _ _ _ => h.shrinks (shrinks_battle r g neg p k sl t)
  | .combat _ p atk blocks neg _ => h.shrinks (shrinks_combat r g neg p atk blocks)
  | .mend _ => h.shrinks (shrinks_mend g)
  | .discard _ p c hc => h.shrinks fun q => by
      by_cases hq : q = p
      · subst hq
        have hlen := List.length_erase_of_mem hc
        have hpos := List.length_pos_of_mem hc
        refine PShrinks.of_sublist ?_ (by simp) (by simp)
        simp only [State.set_same, PState.size, List.length_append, List.length_singleton, hlen]
        omega
      · rw [State.set_other _ _ hq]; exact Shrinks.refl g q
  | .settle _ neg => h.shrinks (shrinks_sweep r g neg)

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
