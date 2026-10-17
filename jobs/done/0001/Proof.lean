-- 闇属性のモンスターはモンスターなので、自動の★「自分のフィールド上のモンスターは最大5枚」から従う

/-- 条件を強めると、数える枚数は増えない -/
theorem countWhere_le_fieldCount (s : PState) :
    countWhere rules claim.matches s ≤ fieldCount rules (some "モンスター") s := by
  unfold countWhere fieldCount
  apply CardGen.System.length_filter_le_of_imp
  intro sl _ h
  simp only [Bool.and_eq_true] at h ⊢
  refine ⟨h.1, ?_⟩
  have hm := h.2
  simp only [claim, CustomClaim.matches, Bool.and_eq_true, Bool.or_eq_true] at hm
  simp only [Option.all_some, beq_iff_eq]
  exact (by simpa using hm.1 : sl.card.type = "モンスター").symm

theorem job_proof : JobStatement := by
  intro decks hd _ g hg
  show ∀ p, countWhere rules claim.matches (g p) ≤ 5
  intro p
  have hb : rules.bounded (some "モンスター") = true := by decide
  have h5 : rules.bound (some "モンスター") = 5 := by decide
  have := fieldCount_le_bound (hg.inv hd) p hb
  rw [h5] at this
  exact Nat.le_trans (countWhere_le_fieldCount _) this
