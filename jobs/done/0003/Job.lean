import CardGen
open CardGen

/-! 証明のジョブ 0003：デッキの魔法は各プレイヤー最大35枚 -/

namespace Job_0003

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
                     excludeSelf := false }] },
   { name := "一斉送還",
     type := "魔法",
     tags := [],
     effects := [CardGen.Effect.activated
                   [CardGen.Action.bounce
                      { types := ["モンスター"],
                        tags := [],
                        side := CardGen.Side.opp,
                        faceUpOnly := false,
                        excludeSelf := false }]] },
   { name := "二枚引き",
     type := "魔法",
     tags := [],
     effects := [CardGen.Effect.activated [CardGen.Action.draw 2]] }]

def claim : CustomClaim := 
  { title := "デッキの魔法は各プレイヤー最大35枚",
    types := ["魔法"],
    tags := [],
    both := false,
    n := 35,
    place := CardGen.Place.deck }

/-- 証明すべき文 -/
def JobStatement : Prop := claim.Statement rules cards

-- デッキの枚数は開始時の35枚を超えない（自動の★の型 E、盤面の制約 `Inv.deck`）ので、条件に合うカードも35枚まで

theorem job_proof : JobStatement := by
  intro decks hd _ g hg
  show ∀ p, (((g p).deck.filter claim.matches).length ≤ 35)
  intro p
  have h := (hg.inv hd).deck p
  have h35 : rules.deckSize - rules.handSize = 35 := by decide
  rw [h35] at h
  exact Nat.le_trans (List.length_filter_le _ _) h

-- 受け入れの確認：証明したのは JobStatement そのもの
example : JobStatement := job_proof
#print axioms job_proof

end Job_0003
