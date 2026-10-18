import CardGen
open CardGen

/-! 証明のジョブ 0002：フィールド全体に闇属性の罠は存在しない -/

namespace Job_0002

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
  { title := "フィールド全体に闇属性の罠は存在しない", types := ["罠"], tags := ["闇属性"], both := true, n := 0 }

/-- 証明すべき文 -/
def JobStatement : Prop := claim.Statement rules cards

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

-- 受け入れの確認：証明したのは JobStatement そのもの
example : JobStatement := job_proof
#print axioms job_proof

end Job_0002
