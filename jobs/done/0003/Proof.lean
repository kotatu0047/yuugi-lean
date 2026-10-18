-- デッキの枚数は開始時の35枚を超えない（自動の★の型 E、盤面の制約 `Inv.deck`）ので、条件に合うカードも35枚まで

theorem job_proof : JobStatement := by
  intro decks hd _ g hg
  show ∀ p, (((g p).deck.filter claim.matches).length ≤ 35)
  intro p
  have h := (hg.inv hd).deck p
  have h35 : rules.deckSize - rules.handSize = 35 := by decide
  rw [h35] at h
  exact Nat.le_trans (List.length_filter_le _ _) h
