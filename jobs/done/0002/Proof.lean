-- カードの一覧に闇属性の罠はない。盤面のカードはどれも一覧から来る（ライブラリの `Reachable.fromPool`）

theorem job_proof : JobStatement := by
  intro decks _ hpool g hg
  have hnone : ∀ c ∈ cards, claim.matches c = false := by decide
  have hzero : ∀ q, countWhere rules claim.matches (g q) = 0 := by
    intro q
    unfold countWhere
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro sl hsl h
    have hc := (hg.fromPool hpool).field hsl
    simp [hnone _ hc] at h
  show countWhere rules claim.matches (g true) + countWhere rules claim.matches (g false) ≤ 0
  simp [hzero]
