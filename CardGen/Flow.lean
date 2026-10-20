import CardGen.TurnProps

/-!
# カードの流れ（どのゲームでも成り立つ★）

どの動きも、カードをプレイヤーの中で移すだけで、デッキは上から引くだけ、墓地には後ろに加えるだけである。
そこで、動きの前後の1人分の状態について、次の3つをまとめて示す（`Step.flow`）。

- カードは並べ替えただけ：デッキ・手札・墓地・フィールドを合わせたカードの、名前ごとの枚数は変わらない
- デッキは上から減るだけ：動きの後のデッキは、動きの前のデッキの後ろの部分（並びは変わらない）
- 墓地は後ろに加わるだけ：動きの前の墓地は、動きの後の墓地の前の部分（墓地のカードは減らず、並びも変わらない）

ここから、ゲームのルールやカードによらない★が出る。

| ★ | 定理 |
|---|---|
| 各プレイヤーのカードは、名前ごとの枚数が開始時のデッキのまま（相手のカードが来ることはない） | `Reachable.cards_perm` |
| デッキの並びは変わらず、上から減るだけ | `Reachable.deck_suffix` |
| 墓地のカードは減らず、並びも変わらない | `Step.grave_prefix`・`Match.step?_grave_prefix` |
-/

namespace CardGen

/-- 1人分の状態の、動きの前後の関係 -/
structure PFlow (s s' : PState) : Prop where
  /-- カードは並べ替えただけ -/
  perm : s'.cards.Perm s.cards
  /-- デッキは上から減るだけ -/
  deck : s'.deck <:+ s.deck
  /-- 墓地は後ろに加わるだけ -/
  grave : s.grave <+: s'.grave

theorem PFlow.refl (s : PState) : PFlow s s := ⟨List.Perm.refl _, List.suffix_refl _, List.prefix_refl _⟩

theorem PFlow.trans {a b c : PState} (h1 : PFlow a b) (h2 : PFlow b c) : PFlow a c :=
  ⟨h2.perm.trans h1.perm, h2.deck.trans h1.deck, h1.grave.trans h2.grave⟩

/-- デッキ・手札・墓地と、フィールドのカード（ダメージなどを除く）が変わらない -/
theorem PFlow.same {s s' : PState} (hd : s'.deck = s.deck) (hh : s'.hand = s.hand) (hg : s'.grave = s.grave)
    (hf : s'.field.map (·.card) = s.field.map (·.card)) : PFlow s s' := by
  refine ⟨?_, by rw [hd]; exact List.suffix_refl _, by rw [hg]; exact List.prefix_refl _⟩
  simp only [PState.cards, hd, hh, hg, hf]
  exact List.Perm.refl _

/-- どのプレイヤーについても `PFlow` -/
def Flow (g g' : State) : Prop := ∀ q, PFlow (g q) (g' q)

theorem Flow.refl (g : State) : Flow g g := fun q => PFlow.refl (g q)

theorem Flow.trans {a b c : State} (h1 : Flow a b) (h2 : Flow b c) : Flow a c := fun q => (h1 q).trans (h2 q)

theorem Flow.set {g : State} {p : PlayerId} {s : PState} (h : PFlow (g p) s) : Flow g (g.set p s) := by
  intro q
  by_cases hq : q = p
  · subst hq; rw [State.set_same]; exact h
  · rw [State.set_other _ _ hq]; exact PFlow.refl _

theorem Flow.map {g : State} {f : PlayerId → PState → PState} (h : ∀ q, PFlow (g q) (f q (g q))) :
    Flow g (g.map f) := by
  intro q; rw [State.map_apply]; exact h q

/-! ## 枚数の数え方 -/

/-- 条件に合うものと合わないものに分けても、名前ごとの枚数は同じ -/
theorem count_split {α β} [BEq β] (p : α → Bool) (l : List α) (f : α → β) (a : β) :
    ((l.filter p).map f).count a + ((l.filter (fun x => !p x)).map f).count a = (l.map f).count a := by
  rw [← List.count_append, ← List.map_append]
  exact ((List.filter_append_perm p l).map f).count_eq a

/-- `k` 番目を取り除いて、後ろに加え直しても、名前ごとの枚数は同じ -/
theorem count_eraseIdx {α β} [BEq β] (f : α → β) {l : List α} {k : Nat} {x : α} (h : l[k]? = some x) (a : β) :
    ((l.eraseIdx k).map f).count a + [f x].count a = (l.map f).count a := by
  obtain ⟨hk, rfl⟩ := List.getElem?_eq_some_iff.1 h
  have e : l = l.take k ++ l[k] :: l.drop (k + 1) := by
    rw [← List.drop_eq_getElem_cons hk, List.take_append_drop]
  rw [List.eraseIdx_eq_take_drop_succ]
  conv => rhs; rw [e]
  simp only [List.map_append, List.map_cons, List.count_append, List.count_cons, List.count_nil]
  omega

/-! ## 1人分の動き -/

theorem pflow_destroy (r : Rules) (sel : Selector) (q : PlayerId) (src : Src) (s : PState) :
    PFlow s (s.destroy r sel q src) := by
  refine ⟨List.perm_iff_count.2 fun a => ?_, List.suffix_refl _, List.prefix_append _ _⟩
  have := count_split (fun sl : Slot => r.onFieldZone sl.zone && sel.matches (sl.view r q src)) s.field (·.card) a
  simp only [PState.cards, PState.destroy, List.count_append] at this ⊢
  omega

theorem pflow_counter (r : Rules) (sel : Selector) (q : PlayerId) (src : Src) (s : PState) :
    PFlow s (s.counter r sel q src) := by
  refine ⟨List.perm_iff_count.2 fun a => ?_, List.suffix_refl _, List.prefix_append _ _⟩
  have := count_split (fun sl : Slot => !r.onFieldZone sl.zone && sel.matches (sl.view r q src)) s.field (·.card) a
  simp only [PState.cards, PState.counter, List.count_append] at this ⊢
  omega

theorem pflow_bounce (r : Rules) (sel : Selector) (q : PlayerId) (src : Src) (s : PState) :
    PFlow s (s.bounce r sel q src) := by
  refine ⟨List.perm_iff_count.2 fun a => ?_, List.suffix_refl _, List.prefix_refl _⟩
  have := count_split (fun sl : Slot => r.onFieldZone sl.zone && sel.matches (sl.view r q src)) s.field (·.card) a
  simp only [PState.cards, PState.bounce, List.count_append] at this ⊢
  omega

theorem pflow_drawN (n : Nat) (s : PState) : PFlow s (s.drawN n) := by
  refine ⟨List.perm_iff_count.2 fun a => ?_, List.drop_suffix _ _, List.prefix_refl _⟩
  have := congrArg (List.count a) (List.take_append_drop n s.deck)
  simp only [PState.cards, PState.drawN, List.count_append] at this ⊢
  omega

theorem pflow_damage (n : Nat) (s : PState) : PFlow s (s.damage n) := PFlow.same rfl rfl rfl rfl

theorem pflow_mark (d : Nat → Nat) (s : PState) : PFlow s (s.mark d) := by
  refine PFlow.same rfl rfl rfl ?_
  have := congrArg (List.map Slot.card) (PState.map_base_mark d s)
  simpa [List.map_map, Function.comp_def] using this

theorem pflow_pump (d : Nat → Int × Int) (s : PState) : PFlow s (s.pump d) := by
  refine PFlow.same rfl rfl rfl ?_
  have := congrArg (List.map Slot.card) (PState.map_base_pump d s)
  simpa [List.map_map, Function.comp_def] using this

theorem pflow_destroyAt (k : Nat) (s : PState) : PFlow s (s.destroyAt k) := by
  unfold PState.destroyAt
  split
  · rename_i sl hk
    refine ⟨List.perm_iff_count.2 fun a => ?_, List.suffix_refl _, List.prefix_append _ _⟩
    have := count_eraseIdx (·.card) hk a
    simp only [PState.cards, List.count_append] at this ⊢
    omega
  · exact PFlow.refl s

theorem pflow_sweep (dead : Nat → Slot → Bool) (s : PState) : PFlow s (s.sweep dead) := by
  refine ⟨List.perm_iff_count.2 fun a => ?_, List.suffix_refl _, List.prefix_append _ _⟩
  have h := count_split (fun x : Slot × Nat => dead x.2 x.1) s.field.zipIdx (fun x => x.1.card) a
  have e : s.field.zipIdx.map (fun x => x.1.card) = s.field.map (·.card) := by
    conv => rhs; rw [← List.zipIdx_map_fst 0 s.field]
    rw [List.map_map]; rfl
  rw [e] at h
  simp only [PState.cards, PState.sweep, List.count_append, List.map_map, Function.comp_def] at h ⊢
  omega

/-! ## 盤面全体の動き -/

theorem flow_sweep (r : Rules) (g : State) (neg : List Pos) : Flow g (g.sweep r neg) :=
  Flow.map fun q => pflow_sweep _ (g q)

theorem flow_mend (g : State) : Flow g g.mend := by
  refine Flow.map fun q => PFlow.same rfl rfl rfl ?_
  simp [List.map_map, Function.comp_def, Slot.base]

theorem flow_strike (r : Rules) (sel : Selector) (n : Nat) (src : Src) (negS : List (PlayerId × Slot)) (g : State) :
    Flow g (g.strike r sel n src negS) :=
  have h : Flow g (g.strikeMarks r sel n src) := Flow.map fun q => pflow_mark _ (g q)
  h.trans (flow_sweep _ _ _)

theorem flow_pumpAll (r : Rules) (sel : Selector) (a d : Int) (src : Src) (negS : List (PlayerId × Slot))
    (g : State) : Flow g (g.pumpAll r sel a d src negS) :=
  have h : Flow g (g.pumpMarks r sel a d src) := Flow.map fun q => pflow_pump _ (g q)
  h.trans (flow_sweep _ _ _)

theorem flow_applyAction (r : Rules) (src : Src) (negS : List (PlayerId × Slot)) (g : State) (a : Action) :
    Flow g (g.applyAction r src negS a) := by
  cases a with
  | destroy sel => exact Flow.map fun q => pflow_destroy r sel q src (g q)
  | bounce sel => exact Flow.map fun q => pflow_bounce r sel q src (g q)
  | draw n => exact Flow.set (pflow_drawN n (g src.p))
  | damage n => exact Flow.set (pflow_damage n (g (!src.p)))
  | heal n => exact Flow.set (PFlow.same rfl rfl rfl rfl)
  | strike sel n => exact flow_strike r sel n src negS g
  | pump sel a d => exact flow_pumpAll r sel a d src negS g
  | counter sel => exact Flow.map fun q => pflow_counter r sel q src (g q)

theorem flow_foldl (r : Rules) (src : Src) (negS : List (PlayerId × Slot)) (as : List Action) (g : State) :
    Flow g (as.foldl (State.applyAction r src negS) g) := by
  induction as generalizing g with
  | nil => exact Flow.refl g
  | cons a t ih => exact (flow_applyAction r src negS g a).trans (ih _)

theorem flow_duel (r : Rules) (g : State) (neg : List Pos) (p : PlayerId) (k : Nat) (sl : Slot)
    (t : Option Nat) : Flow g (g.duel r neg p k sl t) := by
  have dd : ∀ (j n : Nat) (s : PState), PFlow s ((s.destroyAt j).damage n) :=
    fun j n s => (pflow_destroyAt j s).trans (pflow_damage n _)
  cases t with
  | none => exact Flow.set (pflow_damage _ _)
  | some j =>
    simp only [State.duel]
    split
    · exact Flow.refl g
    · split
      · split
        · exact Flow.set (dd _ _ _)
        · split
          · exact Flow.set (dd _ _ _)
          · split
            · exact Flow.refl g
            · have hne : (!p) ≠ p := by cases p <;> decide
              refine (Flow.set (pflow_destroyAt k (g p))).trans (Flow.set ?_)
              rw [State.set_other _ _ hne]
              exact pflow_destroyAt _ _
      · split
        · exact Flow.set (pflow_destroyAt _ _)
        · split
          · exact Flow.set (pflow_damage _ _)
          · exact Flow.refl g

theorem flow_combat (r : Rules) (g : State) (neg : List Pos) (p : PlayerId) (atk : List Nat)
    (blocks : List (Nat × Nat)) : Flow g (g.combat r neg p atk blocks) := by
  simp only [State.combat]
  refine Flow.trans ?_ (flow_sweep _ _ _)
  have hne : (!p) ≠ p := by cases p <;> decide
  refine (Flow.set (pflow_mark _ _)).trans (Flow.set ?_)
  rw [State.set_other _ _ hne]
  exact (pflow_mark _ _).trans (pflow_damage _ _)

theorem flow_battle (r : Rules) (g : State) (neg : List Pos) (p : PlayerId) (k : Nat) (sl : Slot)
    (t : Option Nat) : Flow g (g.battle r neg p k sl t) := by
  unfold State.battle
  split
  · exact flow_combat r g neg p _ _
  · exact flow_duel r g neg p k sl t

/-- 発動した効果の解決：カードはいったんフィールドから離れ、効果の動きのあとで墓地の後ろに加わる -/
theorem flow_resolve (r : Rules) (p : PlayerId) (g : State) {k : Nat} {sl : Slot} (as : List Action)
    (apply : Bool) (neg : List Pos) (tgt : Option Pos) (hk : (g p).field[k]? = some sl) :
    Flow g (g.resolve r p k sl as apply neg tgt) := by
  let g1 := g.set p { g p with field := (g p).field.eraseIdx k }
  let g2 := if apply then as.foldl (State.applyAction r (g.srcOf r p sl tgt) (g.negSlots neg)) g1 else g1
  have h12 : Flow g1 g2 := by
    by_cases ha : apply
    · simp only [g2, ha, ite_true]; exact flow_foldl r _ _ as g1
    · simp only [g2, ha]; exact Flow.refl g1
  have hr : g.resolve r p k sl as apply neg tgt = g2.set p { g2 p with grave := (g2 p).grave ++ [sl.card] } := rfl
  rw [hr]
  intro q
  by_cases hq : q = p
  · subst hq
    rw [State.set_same]
    have h := h12 q
    have e1 : g1 q = { g q with field := (g q).field.eraseIdx k } := State.set_same _ _ _
    rw [e1] at h
    refine ⟨List.perm_iff_count.2 fun a => ?_, h.deck, h.grave.trans (List.prefix_append _ _)⟩
    have hc := h.perm.count_eq a
    have he := count_eraseIdx (·.card) hk a
    simp only [PState.cards, List.count_append] at hc he ⊢
    omega
  · rw [State.set_other _ _ hq]
    have h := h12 q
    rwa [show g1 q = g q from State.set_other _ _ hq] at h

/-! ## どの動きでも -/

/-- **どの動きでも、カードは並べ替えただけ・デッキは上から減るだけ・墓地は後ろに加わるだけ** -/
theorem Step.flow {r : Rules} {g g' : State} : Step r g g' → Flow g g'
  | .draw _ p c d hd => Flow.set (by
      refine ⟨List.perm_iff_count.2 fun a => ?_, by rw [hd]; exact List.suffix_cons _ _, List.prefix_refl _⟩
      simp only [PState.cards, hd, List.count_append, List.count_cons, List.count_nil]
      omega)
  | .place _ p c i _ z up hc _ _ _ _ _ => Flow.set (by
      refine ⟨List.perm_iff_count.2 fun a => ?_, List.suffix_refl _, List.prefix_refl _⟩
      have := (List.perm_cons_erase hc).count_eq a
      simp only [PState.cards, List.map_append, List.map_cons, List.map_nil, List.count_append,
        List.count_cons, List.count_nil] at this ⊢
      omega)
  | .resolve _ p k sl as apply neg tgt hk _ => flow_resolve r p g as apply neg tgt hk
  | .attack _ p k sl t neg _ _ _ _ => flow_battle r g neg p k sl t
  | .combat _ p atk blocks neg _ => flow_combat r g neg p atk blocks
  | .mend _ => flow_mend g
  | .trigger _ p _ _ _ as cell apply neg tgt _ _ => by
      unfold State.fire
      split
      · exact flow_foldl r _ _ as g
      · exact Flow.refl g
  | .discard _ p c hc => Flow.set (by
      refine ⟨List.perm_iff_count.2 fun a => ?_, List.suffix_refl _, List.prefix_append _ _⟩
      have := (List.perm_cons_erase hc).count_eq a
      simp only [PState.cards, List.count_append, List.count_cons, List.count_nil] at this ⊢
      omega)
  | .settle _ neg => flow_sweep r g neg

/-- 開始時の状態から、到達できるどの状態へも -/
theorem Reachable.flow {r : Rules} {decks : PlayerId → List Card} {g : State} (hg : Reachable r decks g) :
    Flow (CardGen.start r decks) g := by
  induction hg with
  | start => exact Flow.refl _
  | step _ hs ih => exact ih.trans hs.flow

/-- **各プレイヤーの、デッキ・手札・墓地・フィールドを合わせたカードは、開始時のデッキを並べ替えたもの**
（名前ごとの枚数が同じ。相手のカードが自分のところに来ることはない） -/
theorem Reachable.cards_perm {r : Rules} {decks : PlayerId → List Card} {g : State} (hg : Reachable r decks g)
    (p : PlayerId) : (g p).cards.Perm (decks p) := by
  refine (hg.flow p).perm.trans ?_
  simp only [CardGen.start, PState.cards, List.append_nil, List.map_nil]
  exact List.perm_append_comm.trans (by rw [List.take_append_drop])

/-- **デッキの並びは変わらず、上から減るだけ**（いつも、開始時のデッキの後ろの部分） -/
theorem Reachable.deck_suffix {r : Rules} {decks : PlayerId → List Card} {g : State} (hg : Reachable r decks g)
    (p : PlayerId) : (g p).deck <:+ (decks p).drop r.handSize :=
  (hg.flow p).deck

/-- **どの動きでも、墓地のカードは減らず、並びも変わらない**（動きの前の墓地は、動きの後の墓地の前の部分） -/
theorem Step.grave_prefix {r : Rules} {g g' : State} (h : Step r g g') (p : PlayerId) :
    (g p).grave <+: (g' p).grave :=
  (h.flow p).grave

/-! ## ターンのある対戦 -/

theorem flow_drawUpTo (r : Rules) (p : PlayerId) : ∀ (n : Nat) (g : State), Flow g (g.drawUpTo r p n)
  | 0, g => Flow.refl g
  | n + 1, g => by
    unfold State.drawUpTo
    split
    · rename_i g' hg
      exact (Step.flow (step?_sound hg)).trans (flow_drawUpTo r p n g')
    · exact Flow.refl g

/-- ターンのある対戦の1つの動き（ターンの終わりのドローも含む）でも、カードの流れは同じ -/
theorem Match.step?_flow {r : Rules} {m m' : Match} {ch : TChoice} (hs : m.step? r ch = some m') :
    Flow m.g m'.g := by
  obtain ⟨m0, _, _, _, ⟨-, rfl, -⟩ | ⟨hmv, -⟩, rfl⟩ := Match.step?_moved hs
  · exact Flow.refl _
  show Flow m.g m0.g
  cases hmv with
  | place _ _ hg => exact Step.flow (step?_sound hg)
  | cast _ _ hg => exact Step.flow (step?_sound hg)
  | resolve hg => exact Step.flow (step?_sound hg)
  | settle => exact Step.flow (.settle _ _)
  | discard hg => exact Step.flow (step?_sound hg)
  | trigger _ hg => exact Step.flow (step?_sound hg)
  | skip => exact Flow.refl _
  | attack _ hg => exact Step.flow (step?_sound hg)
  | declare _ => exact Flow.refl _
  | block hg => exact Step.flow (step?_sound hg)
  | tap _ _ => exact Flow.refl _
  | oppTap _ _ => exact Flow.refl _
  | endTurn => exact (Step.flow (r := r) (.mend _)).trans (flow_drawUpTo r _ _ _)

/-- **ターンのある対戦のどの動きでも、墓地のカードは減らず、並びも変わらない** -/
theorem Match.step?_grave_prefix {r : Rules} {m m' : Match} {ch : TChoice} (hs : m.step? r ch = some m')
    (p : PlayerId) : (m.g p).grave <+: (m'.g p).grave :=
  (Match.step?_flow hs p).grave

end CardGen
