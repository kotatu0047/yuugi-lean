import CardGen
open CardGen

/-! 証明のジョブ 0001：自分のフィールド上の闇属性のモンスターは最大5枚 -/

namespace Job_0001

def rules : Rules := 
  { cardTypes := ["モンスター", "魔法", "罠"],
    deckSize := 40,
    handSize := 5,
    zones := [{ name := "モンスターカードゾーン",
                count := 5,
                capacity := CardGen.Capacity.one,
                role := CardGen.ZoneRole.plain,
                onField := true,
                admits := ["モンスター"] },
              { name := "魔法罠ゾーン",
                count := 5,
                capacity := CardGen.Capacity.one,
                role := CardGen.ZoneRole.plain,
                onField := true,
                admits := ["魔法", "罠"] },
              { name := "デッキゾーン",
                count := 1,
                capacity := CardGen.Capacity.many,
                role := CardGen.ZoneRole.deck,
                onField := false,
                admits := ["モンスター", "魔法", "罠"] },
              { name := "墓地ゾーン",
                count := 1,
                capacity := CardGen.Capacity.many,
                role := CardGen.ZoneRole.grave,
                onField := false,
                admits := ["モンスター", "魔法", "罠"] }] }

def cards : List Card := 
  [{ name := "サンダー・ボルト",
     type := "魔法",
     tags := [],
     effects := [CardGen.Effect.activated
                   [CardGen.Action.destroy
                      { types := ["モンスター"],
                        tags := [],
                        side := CardGen.Side.opp,
                        faceUpOnly := false,
                        excludeSelf := false }]] },
   { name := "ハーピィの羽根帚",
     type := "魔法",
     tags := [],
     effects := [CardGen.Effect.activated
                   [CardGen.Action.destroy
                      { types := ["魔法", "罠"],
                        tags := [],
                        side := CardGen.Side.opp,
                        faceUpOnly := false,
                        excludeSelf := false }]] },
   { name := "スキルドレイン",
     type := "罠",
     tags := [],
     effects := [CardGen.Effect.negate
                   { types := ["モンスター"],
                     tags := [],
                     side := CardGen.Side.both,
                     faceUpOnly := true,
                     excludeSelf := false }] },
   { name := "王宮のお触れ",
     type := "罠",
     tags := [],
     effects := [CardGen.Effect.negate
                   { types := ["罠"],
                     tags := [],
                     side := CardGen.Side.both,
                     faceUpOnly := true,
                     excludeSelf := true }] },
   { name := "人造人間－サイコ・ショッカー",
     type := "モンスター",
     tags := ["闇属性", "機械族"],
     effects := [CardGen.Effect.negate
                   { types := ["罠"],
                     tags := [],
                     side := CardGen.Side.both,
                     faceUpOnly := true,
                     excludeSelf := false }] },
   { name := "D－HERO Bloo－D",
     type := "モンスター",
     tags := ["闇属性", "戦士族"],
     effects := [CardGen.Effect.negate
                   { types := ["モンスター"],
                     tags := [],
                     side := CardGen.Side.opp,
                     faceUpOnly := true,
                     excludeSelf := false }] }]

def claim : CustomClaim := 
  { title := "自分のフィールド上の闇属性のモンスターは最大5枚", types := ["モンスター"], tags := ["闇属性"], both := false, n := 5 }

/-- 証明すべき文 -/
def JobStatement : Prop := claim.Statement rules cards

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

-- 受け入れの確認：証明したのは JobStatement そのもの
example : JobStatement := job_proof
#print axioms job_proof

end Job_0001
