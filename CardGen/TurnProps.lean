import CardGen.Turn

/-!
# ターンのある対戦の定理

`Turn.lean` のターンのある対戦（`TReachable`）について示す。

- 盤面はターンのないモデルで到達できる（`TReachable.reachable`）。だから盤面の制約・★・受け入れた証明のジョブは
  そのまま成り立つ（`TReachable.of_reachable`）
- 召喚の上限（`summons_le`）・種類ごとの上限（`placed_le`）・記録はフィールドのカードの一部（`fits`）
- マナの収支（`mana_balance`・`spent_le`）と色（`mana_from`）
- 優先権のパスの回数（`passes_le`）・スタックのカードは場にある（`stack_fits`）・
  対戦の終わり（`Match.step?_over`）・ターンの終わりの後始末（`Match.endTurn_clean`）
-/

namespace CardGen

variable {r : Rules} {decks : PlayerId → List Card} {first : PlayerId} {m : Match}
/-! ## ターンのない対戦への引き継ぎ -/

theorem Reachable.drawUpTo (p : PlayerId) :
    ∀ (n : Nat) {g : State}, Reachable r decks g → Reachable r decks (g.drawUpTo r p n)
  | 0, _, h => h
  | n + 1, g, h => by
    unfold State.drawUpTo
    split
    · rename_i g' hg
      exact Reachable.drawUpTo p n (h.step (step?_sound hg))
    · exact h

/-- **ターンのある対戦の盤面は、どれもターンのないモデルで到達できる盤面** -/
theorem TReachable.reachable (h : TReachable r decks first m) : Reachable r decks m.g := by
  induction h with
  | start =>
    simp only [Match.start]
    split
    · exact Reachable.drawUpTo first _ .start
    · exact .start
  | step ch _ hs ih =>
    obtain ⟨m0, _, _, ⟨-, rfl⟩ | hmv, rfl⟩ := Match.step?_moved hs
    · exact ih
    show Reachable r decks m0.g
    cases hmv with
    | place _ _ hg => exact ih.step (step?_sound hg)
    | cast _ _ hg => exact ih.step (step?_sound hg)
    | resolve hg => exact ih.step (step?_sound hg)
    | settle => exact ih.step (.settle _ _)
    | attack _ hg => exact ih.step (step?_sound hg)
    | declare _ => exact ih
    | block hg => exact ih.step (step?_sound hg)
    | tap _ _ => exact ih
    | oppTap _ _ => exact ih
    | endTurn => exact Reachable.drawUpTo _ _ (ih.step (.mend _))

/-- **ターンのない対戦のどの盤面でも成り立つ性質は、ターンのある対戦でも成り立つ**
（盤面の制約、★、受け入れた証明のジョブなど） -/
theorem TReachable.of_reachable {P : State → Prop} (hP : ∀ g, Reachable r decks g → P g)
    (h : TReachable r decks first m) : P m.g :=
  hP _ h.reachable

/-! ## ターンがあるから言える性質 -/

@[simp] theorem TurnInfo.prune_tp (t : TurnInfo) (g : State) : (t.prune g).tp = t.tp := rfl
@[simp] theorem TurnInfo.prune_summons (t : TurnInfo) (g : State) : (t.prune g).summons = t.summons := rfl
@[simp] theorem TurnInfo.prune_placed (t : TurnInfo) (g : State) : (t.prune g).placed = t.placed := rfl
@[simp] theorem TurnInfo.prune_pool (t : TurnInfo) (g : State) : (t.prune g).pool = t.pool := rfl
@[simp] theorem TurnInfo.prune_oppPool (t : TurnInfo) (g : State) : (t.prune g).oppPool = t.oppPool := rfl
@[simp] theorem TurnInfo.prune_made (t : TurnInfo) (g : State) : (t.prune g).made = t.made := rfl
@[simp] theorem TurnInfo.prune_spent (t : TurnInfo) (g : State) : (t.prune g).spent = t.spent := rfl
@[simp] theorem TurnInfo.pop_summons (r : Rules) (t : TurnInfo) : (t.pop r).summons = t.summons := by
  unfold TurnInfo.pop; split <;> rfl
@[simp] theorem TurnInfo.pop_placed (r : Rules) (t : TurnInfo) : (t.pop r).placed = t.placed := by
  unfold TurnInfo.pop; split <;> rfl
@[simp] theorem TurnInfo.pop_pool (r : Rules) (t : TurnInfo) : (t.pop r).pool = t.pool := by
  unfold TurnInfo.pop; split <;> rfl
@[simp] theorem TurnInfo.pop_oppPool (r : Rules) (t : TurnInfo) : (t.pop r).oppPool = t.oppPool := by
  unfold TurnInfo.pop; split <;> rfl
@[simp] theorem TurnInfo.pop_made (r : Rules) (t : TurnInfo) : (t.pop r).made = t.made := by
  unfold TurnInfo.pop; split <;> rfl
@[simp] theorem TurnInfo.pop_spent (r : Rules) (t : TurnInfo) : (t.pop r).spent = t.spent := by
  unfold TurnInfo.pop; split <;> rfl

/-- **1ターンに置いた戦闘できるカードの枚数は、上限を超えない**（上限があるとき） -/
theorem TReachable.summons_le (h : TReachable r decks first m) (hl : r.summonsPerTurn ≠ 0) :
    m.turn.summons ≤ r.summonsPerTurn := by
  induction h with
  | start => simp [Match.start]
  | step ch _ hs ih =>
    obtain ⟨m0, _, _, ⟨-, rfl⟩ | hmv, rfl⟩ := Match.step?_moved hs
    · simpa using ih
    simp only [TurnInfo.withPrio_summons]
    cases hmv with
    | @place _ _ _ _ _ c _ hc hok _ =>
      simp only [TurnInfo.placeOK, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
        beq_iff_eq, decide_eq_true_eq] at hok
      simp only [TurnInfo.prune_summons, TurnInfo.afterPlace]
      split
      · rename_i hf
        rcases hok.1.1.2 with (h1 | h1) | h1
        · simp [hf] at h1
        · exact absurd h1 hl
        · omega
      · simpa using ih
    | cast _ _ _ => simpa [TurnInfo.afterCast] using ih
    | resolve _ => simpa using ih
    | settle => simpa using ih
    | attack _ _ => simpa [TurnInfo.afterAttack] using ih
    | declare _ => simpa [TurnInfo.afterAttack] using ih
    | block _ => simpa [TurnInfo.afterBlock] using ih
    | tap _ _ => simpa [TurnInfo.afterTap] using ih
    | oppTap _ _ => simpa [TurnInfo.afterOppTap] using ih
    | endTurn => simp [TurnInfo.prune, TurnInfo.next]

/-- **種類ごとの上限：1ターンに置いた、その種類のカードの枚数は上限を超えない**（例：土地は1ターンに1枚） -/
theorem TReachable.placed_le (h : TReachable r decks first m) {l : PlaceLimit} (hl : l ∈ r.placeLimits) :
    (m.turn.placed.filter l.types.contains).length ≤ l.count := by
  induction h with
  | start => simp [Match.start]
  | step ch _ hs ih =>
    obtain ⟨m0, _, _, ⟨-, rfl⟩ | hmv, rfl⟩ := Match.step?_moved hs
    · simpa using ih
    simp only [TurnInfo.withPrio_placed]
    cases hmv with
    | @place _ _ _ _ _ c _ _ hok _ =>
      simp only [TurnInfo.placeOK, Bool.and_eq_true, List.all_eq_true] at hok
      have := hok.1.2 l hl
      simp only [TurnInfo.prune_placed, TurnInfo.afterPlace, List.filter_append, List.length_append]
      simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at this
      rcases this with h1 | h1
      · have : c.type ∉ l.types := by simpa using h1
        simpa [List.filter_cons, this] using ih
      · simp only [List.filter_cons, List.filter_nil]
        split <;> simp <;> omega
    | cast _ _ _ => simpa [TurnInfo.afterCast] using ih
    | resolve _ => simpa using ih
    | settle => simpa using ih
    | attack _ _ => simpa [TurnInfo.afterAttack] using ih
    | declare _ => simpa [TurnInfo.afterAttack] using ih
    | block _ => simpa [TurnInfo.afterBlock] using ih
    | tap _ _ => simpa [TurnInfo.afterTap] using ih
    | oppTap _ _ => simpa [TurnInfo.afterOppTap] using ih
    | endTurn => simp [TurnInfo.prune, TurnInfo.next]

/-- 記録はどれも、フィールドのカード（ダメージを除いたもの）の一部（同じカードの枚数も含めて） -/
def TurnInfo.Fits (t : TurnInfo) (g : State) : Prop :=
  BagLe t.attacked (g t.tp).bases ∧ BagLe t.entered (g t.tp).bases ∧ BagLe t.tapped (g t.tp).bases ∧
    BagLe t.oppTapped (g (!t.tp)).bases ∧ BagLe t.blocked (g (!t.tp)).bases ∧ BagLe t.attackers (g t.tp).bases

theorem TurnInfo.prune_fits (t : TurnInfo) (g : State) : (t.prune g).Fits g :=
  ⟨prune_bagLe _ _, prune_bagLe _ _, prune_bagLe _ _, prune_bagLe _ _, prune_bagLe _ _, prune_bagLe _ _⟩

/-- **攻撃・置いた・タップ・ブロック・攻撃の宣言の記録は、いつもフィールドのカードの一部**
（同じカードの枚数も含めて。だから、フィールドのどのカードも1ターンに1回までしか攻撃できず、
タップしているカードは、起きるまでタップできない） -/
theorem TReachable.fits (h : TReachable r decks first m) : m.turn.Fits m.g := by
  induction h with
  | start => refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro a <;> simp [Match.start]
  | step ch _ hs ih =>
    obtain ⟨m0, _, _, ⟨-, rfl⟩ | hmv, rfl⟩ := Match.step?_moved hs
    · exact ih
    show m0.turn.Fits m0.g
    cases hmv <;> exact TurnInfo.prune_fits _ _

/-- **攻撃したカードの記録は、ターンプレイヤーのフィールドのカードの一部**
（同じカードの枚数も含めて。だから、フィールドのどのカードも1ターンに1回までしか攻撃できない） -/
theorem TReachable.attacked_bagLe (h : TReachable r decks first m) : BagLe m.turn.attacked (m.g m.turn.tp).bases :=
  h.fits.1

/-! ## マナの収支 -/

theorem bagLeB_count {l m : List String} (h : bagLeB l m = true) (a : String) : l.count a ≤ m.count a := by
  by_cases ha : a ∈ l
  · have := List.all_eq_true.1 h a ha
    simpa using this
  · rw [List.count_eq_zero_of_not_mem ha]; exact Nat.zero_le _

theorem length_foldl_erase : ∀ (l m : List String), (∀ a, l.count a ≤ m.count a) →
    (l.foldl List.erase m).length + l.length = m.length
  | [], m, _ => by simp
  | a :: l, m, h => by
    have ha : a ∈ m := List.count_pos_iff.1 (Nat.lt_of_lt_of_le (by simp) (h a))
    have h' : ∀ b, l.count b ≤ (m.erase a).count b := by
      intro b
      have := h b
      rw [List.count_erase, List.count_cons] at *
      by_cases hb : a = b
      · subst hb; simp at this ⊢; omega
      · have : (a == b) = false := by simpa using hb
        simp_all
    have := length_foldl_erase l (m.erase a) h'
    simp only [List.foldl_cons, List.length_cons, List.length_erase_of_mem ha] at this ⊢
    have := List.length_pos_of_mem ha
    omega

/-- 払ったあとのマナの数 -/
theorem length_pay {c : Card} {pool pay : List String} (h : payOK c pool pay = true) :
    (pay.foldl List.erase pool).length + pay.length = pool.length := by
  simp only [payOK, Bool.and_eq_true] at h
  exact length_foldl_erase pay pool (bagLeB_count h.1.1)

/-- **マナの収支：持っているマナと、払ったマナの合計は、このターンにタップで出したマナに等しい**
（だから、1ターンに払うマナは、そのターンにタップして出したマナを超えない） -/
theorem TReachable.mana_balance (h : TReachable r decks first m) :
    m.turn.pool.length + m.turn.oppPool.length + m.turn.spent = m.turn.made := by
  induction h with
  | start => simp [Match.start]
  | step ch _ hs ih =>
    obtain ⟨m0, _, _, ⟨-, rfl⟩ | hmv, rfl⟩ := Match.step?_moved hs
    · simpa using ih
    simp only [TurnInfo.withPrio_pool, TurnInfo.withPrio_oppPool, TurnInfo.withPrio_spent, TurnInfo.withPrio_made]
    cases hmv with
    | place _ hok _ =>
      simp only [TurnInfo.placeOK, Bool.and_eq_true] at hok
      have := length_pay hok.2
      simp only [TurnInfo.prune_pool, TurnInfo.prune_oppPool, TurnInfo.prune_spent, TurnInfo.prune_made,
        TurnInfo.afterPlace]
      omega
    | cast _ hok _ =>
      simp only [TurnInfo.castOK, Bool.and_eq_true] at hok
      have := length_pay hok.2
      simp only [TurnInfo.prune_pool, TurnInfo.prune_oppPool, TurnInfo.prune_spent, TurnInfo.prune_made,
        TurnInfo.afterCast]
      omega
    | resolve _ => simpa using ih
    | settle => simpa using ih
    | attack _ _ => simpa [TurnInfo.afterAttack] using ih
    | declare _ => simpa [TurnInfo.afterAttack] using ih
    | block _ => simpa [TurnInfo.afterBlock] using ih
    | tap _ _ => simp [TurnInfo.afterTap]; omega
    | oppTap _ _ => simp [TurnInfo.afterOppTap]; omega
    | endTurn => simp [TurnInfo.prune, TurnInfo.next]

/-- **1ターンに払ったマナは、そのターンにタップして出したマナを超えない** -/
theorem TReachable.spent_le (h : TReachable r decks first m) : m.turn.spent ≤ m.turn.made := by
  have := h.mana_balance; omega

/-! ## 優先権・スタック・対戦の終わり・ターンの終わりの性質 -/

theorem TurnInfo.afterPass_passes (t : TurnInfo) (h : t.passes < 2) : t.afterPass.passes ≤ 2 := by
  unfold TurnInfo.afterPass TurnInfo.withPrio
  split
  · simp only; omega
  · split <;> simp

theorem TurnInfo.prioAfter_passes (r : Rules) (b a : TurnInfo) (ch : TChoice) (h : b.passes ≤ 2) :
    (b.prioAfter r a ch).passes ≤ 2 := by
  unfold TurnInfo.prioAfter TurnInfo.withPrio
  split
  · simpa using h
  · simp
  · split <;> simp

/-- **パスの回数はいつも 2 以下**（両者がパスしたら、解決かブロックをするまでパスできない） -/
theorem TReachable.passes_le (h : TReachable r decks first m) : m.turn.passes ≤ 2 := by
  induction h with
  | start => simp [Match.start]
  | @step m m' ch _ hs ih =>
    unfold Match.step? at hs
    split at hs
    · rename_i m1 h1
      cases hs
      show m1.turn.passes ≤ 2
      unfold Match.step1? at h1
      split at h1
      · cases h1
      · split at h1
        · split at h1
          · rename_i hlt; cases h1; exact m.turn.afterPass_passes hlt
          · cases h1
        · split at h1
          · obtain ⟨m2, _, rfl⟩ := Option.map_eq_some_iff.1 h1
            exact m.turn.prioAfter_passes r m2.turn ch ih
          · cases h1
    · cases hs

/-- スタックの記録の、残ったものはどれもフィールドにある -/
theorem pruneStack_mem : ∀ (st : List (PlayerId × Slot)) (f : PlayerId → List Slot),
    ∀ e ∈ pruneStack st f, e.2 ∈ f e.1
  | [], _, e, he => by simp [pruneStack] at he
  | (q, a) :: as, f, e, he => by
    unfold pruneStack at he
    split at he
    · rename_i ha
      rcases List.mem_cons.1 he with rfl | he
      · exact ha
      · have := pruneStack_mem as _ e he
        by_cases hq : e.1 = q
        · simp only [hq, ite_true] at this
          exact hq ▸ List.mem_of_mem_erase this
        · simpa [hq] using this
    · exact pruneStack_mem as f e he

/-- スタックの記録が、どれもフィールドのカード -/
def TurnInfo.StackFits (t : TurnInfo) (g : State) : Prop := ∀ e ∈ t.stack, e.2 ∈ (g e.1).bases

theorem TurnInfo.prune_stackFits (t : TurnInfo) (g : State) : (t.prune g).StackFits g :=
  fun e he => pruneStack_mem t.stack (fun q => (g q).bases) e he

/-- **スタックに積まれたカードは、いつも置いたプレイヤーのフィールド（スタックのゾーン）にある**
（打ち消されたり、手札に戻されたりしたカードは、スタックからも消える） -/
theorem TReachable.stack_fits (h : TReachable r decks first m) : m.turn.StackFits m.g := by
  induction h with
  | start => intro e he; simp [Match.start] at he
  | step ch _ hs ih =>
    obtain ⟨m0, _, _, ⟨-, rfl⟩ | hmv, rfl⟩ := Match.step?_moved hs
    · exact ih
    show m0.turn.StackFits m0.g
    cases hmv <;> exact TurnInfo.prune_stackFits _ _

/-- **対戦が終わったら（ライフが 0 か、デッキ切れ）、それ以上どの動きもできない** -/
theorem Match.step?_over (h : m.over r = true) (ch : TChoice) : m.step? r ch = none := by
  unfold Match.step? Match.step1?
  simp [h]

/-- 引いても、フィールドは変わらない -/
theorem State.drawUpTo_field (r : Rules) (p : PlayerId) :
    ∀ (n : Nat) (g : State) (q : PlayerId), ((g.drawUpTo r p n) q).field = (g q).field
  | 0, _, _ => rfl
  | n + 1, g, q => by
    unfold State.drawUpTo
    cases hg : g.step? r (.draw p) with
    | none => rfl
    | some g' =>
      simp only
      rw [State.drawUpTo_field r p n g' q]
      unfold State.step? at hg
      split at hg
      · rename_i g0 h0
        cases hg
        simp only [State.step0?] at h0
        split at h0
        · cases h0; cases q <;> cases p <;> rfl
        · cases h0
      · cases hg

/-- **ターンの終わりに、どのカードの受けたダメージとターンの終わりまでの変化も消える**
（新しいターンの始めには、フィールドのどのカードもダメージが 0 で、攻撃力・守備力の一時的な変化もない） -/
theorem Match.endTurn_clean {m' : Match} (hs : m.step? r .endTurn = some m') :
    ∀ q, ∀ sl ∈ (m'.g q).field, sl.base = sl := by
  obtain ⟨m0, _, _, ⟨h, -⟩ | hmv, rfl⟩ := Match.step?_moved hs
  · cases h
  cases hmv
  intro q sl hsl
  simp only [State.drawUpTo_field, State.mend, State.map_apply, List.mem_map] at hsl
  obtain ⟨x, -, rfl⟩ := hsl
  rfl

/-! ## マナの色 -/

/-- マナ `c` は、カードの一覧 `cards` のどれかのマナを出すカードが出せる色（`""` は無色） -/
def ManaFrom (cards : List Card) (c : String) : Prop :=
  ∃ card ∈ cards, 0 < card.mana ∧ (c = card.manaColor ∨ c ∈ card.manaChoice)

theorem mem_of_mem_foldl_erase : ∀ (l m : List String) (c : String), c ∈ l.foldl List.erase m → c ∈ m
  | [], _, _, h => h
  | a :: l, m, c, h => List.mem_of_mem_erase (mem_of_mem_foldl_erase l (m.erase a) c h)

theorem manaOut_from {card : Card} {color : String} {out : List String} (h : manaOut card color = some out) :
    ∀ c ∈ out, 0 < card.mana ∧ (c = card.manaColor ∨ c ∈ card.manaChoice) := by
  intro c hc
  unfold manaOut at h
  split at h
  · cases h
    obtain ⟨h1, h2⟩ := List.mem_replicate.1 hc
    exact ⟨Nat.pos_of_ne_zero h1, .inl h2⟩
  · split at h
    · rename_i hch
      cases h
      obtain ⟨h1, rfl⟩ := List.mem_replicate.1 hc
      exact ⟨Nat.pos_of_ne_zero h1, .inr (by simpa using hch)⟩
    · cases h

/-- **持っているマナは、どれも一覧のマナを出すカードが出せる色（か無色）**
（形式の検査で、カードの出すマナの色はルールのマナの色のどれかなので、マナはルールの色か無色だけ） -/
theorem TReachable.mana_from {pool : List Card}
    (hpool : ∀ p, ∀ x ∈ decks p, x ∈ pool) (h : TReachable r decks first m) :
    ∀ c ∈ m.turn.pool ++ m.turn.oppPool, ManaFrom pool c := by
  induction h with
  | start => intro c hc; simp [Match.start] at hc
  | @step m _ ch hm hs ih =>
    obtain ⟨m0, _, _, ⟨-, rfl⟩ | hmv, rfl⟩ := Match.step?_moved hs
    · simpa [TurnInfo.withPrio] using ih
    simp only [TurnInfo.withPrio_pool, TurnInfo.withPrio_oppPool]
    have fp := hm.reachable.fromPool hpool
    cases hmv with
    | place _ _ _ =>
      intro c hc
      simp only [TurnInfo.prune_pool, TurnInfo.prune_oppPool, TurnInfo.afterPlace, List.mem_append] at hc
      rcases hc with hc | hc
      · exact ih c (List.mem_append_left _ (mem_of_mem_foldl_erase _ _ _ hc))
      · exact ih c (List.mem_append_right _ hc)
    | cast _ _ _ =>
      intro c hc
      simp only [TurnInfo.prune_pool, TurnInfo.prune_oppPool, TurnInfo.afterCast, List.mem_append] at hc
      rcases hc with hc | hc
      · exact ih c (List.mem_append_left _ hc)
      · exact ih c (List.mem_append_right _ (mem_of_mem_foldl_erase _ _ _ hc))
    | @tap _ _ sl _ hsl hout =>
      intro c hc
      simp only [TurnInfo.prune_pool, TurnInfo.prune_oppPool, TurnInfo.afterTap, List.mem_append] at hc
      rcases hc with (hc | hc) | hc
      · exact ih c (List.mem_append_left _ hc)
      · exact ⟨sl.card, fp.field (List.mem_of_getElem? hsl), manaOut_from hout c hc⟩
      · exact ih c (List.mem_append_right _ hc)
    | @oppTap _ _ sl _ hsl hout =>
      intro c hc
      simp only [TurnInfo.prune_pool, TurnInfo.prune_oppPool, TurnInfo.afterOppTap, List.mem_append] at hc
      rcases hc with hc | hc | hc
      · exact ih c (List.mem_append_left _ hc)
      · exact ih c (List.mem_append_right _ hc)
      · exact ⟨sl.card, fp.field (List.mem_of_getElem? hsl), manaOut_from hout c hc⟩
    | endTurn => intro c hc; simp [TurnInfo.prune, TurnInfo.next] at hc
    | resolve _ => simpa using ih
    | settle => simpa using ih
    | attack _ _ => simpa [TurnInfo.afterAttack] using ih
    | declare _ => simpa [TurnInfo.afterAttack] using ih
    | block _ => simpa [TurnInfo.afterBlock] using ih

end CardGen
