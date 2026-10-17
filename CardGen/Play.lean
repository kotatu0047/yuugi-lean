import CardGen.Inv

/-!
# 実行できる対戦の1歩

`Step`（証明で使う動きの関係）を、選んだ動きから次の状態を計算する関数 `State.step?` にしたもの。
`step?_sound` により、`step?` で進めた状態はどれも `Step` で進めた状態なので、
`Reachable.inv` や `derived_valid` の保証がそのまま当てはまる。C# のゲームエンジンはこの関数と
同じ結果を出すことを差分テストで確かめる。
-/

namespace CardGen

/-- プレイヤーが選ぶ動き -/
inductive Choice
  /-- `p` がデッキの一番上を引く -/
  | draw (p : PlayerId)
  /-- `p` が手札の `hand` 番目のカードを `zone` 番目のゾーンに置く（`up`：表側表示か） -/
  | place (p : PlayerId) (hand : Nat) (zone : Nat) (up : Bool)
  /-- `p` がフィールドの `k` 番目のカードの `eff` 番目の効果を発動して解決する（`apply`：無効にされていないか） -/
  | resolve (p : PlayerId) (k : Nat) (eff : Nat) (apply : Bool)
deriving Repr, DecidableEq

/-- 選んだ動きをしたあとの状態（できない動きなら `none`） -/
def State.step? (r : Rules) (g : State) : Choice → Option State
  | .draw p =>
    match (g p).deck with
    | c :: d => some (g.set p { g p with deck := d, hand := (g p).hand ++ [c] })
    | [] => none
  | .place p h i up => do
    let c ← (g p).hand[h]?
    let z ← r.zones[i]?
    guard (z.role == .plain && z.admits.contains c.type &&
      (z.capacity != .one || decide (((g p).field.filter (·.zone == i)).length < z.count)))
    return g.set p { g p with hand := (g p).hand.erase c, field := (g p).field ++ [⟨i, c, up⟩] }
  | .resolve p k e apply => do
    let sl ← (g p).field[k]?
    match sl.card.effects[e]? with
    | some (.activated as) => some (g.resolve r p k sl as apply)
    | _ => none

/-- **`step?` で進めた状態は、`Step` で進めた状態** -/
theorem step?_sound {r : Rules} {g g' : State} {ch : Choice} (h : g.step? r ch = some g') : Step r g g' := by
  cases ch with
  | draw p =>
    simp only [State.step?] at h
    split at h
    · rename_i c d hd; cases h; exact .draw g p c d hd
    · cases h
  | place p hi i up =>
    simp only [State.step?, Option.bind_eq_bind] at h
    cases hc : (g p).hand[hi]? with
    | none => simp [hc] at h
    | some c =>
      cases hz : r.zones[i]? with
      | none => simp [hc, hz] at h
      | some z =>
        simp only [hc, hz, Option.bind_some] at h
        by_cases hg : (z.role == .plain && z.admits.contains c.type &&
            (z.capacity != .one || decide (((g p).field.filter (·.zone == i)).length < z.count))) = true
        · simp only [hg, guard, ite_true, Option.pure_def, Option.bind_some] at h
          cases h
          simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, bne_iff_ne, ne_eq,
            decide_eq_true_eq] at hg
          refine .place g p c i z up (List.mem_of_getElem? hc) hz hg.1.1 hg.1.2 fun hcap => ?_
          rcases hg.2 with h1 | h1
          · exact absurd hcap h1
          · exact h1
        · rw [Bool.not_eq_true] at hg
          simp only [hg, guard] at h
          cases h
  | resolve p k e apply =>
    simp only [State.step?, Option.bind_eq_bind] at h
    cases hk : (g p).field[k]? with
    | none => simp [hk] at h
    | some sl =>
      simp only [hk, Option.bind_some] at h
      split at h
      · rename_i as he
        cases h
        exact .resolve g p k sl as apply hk (List.mem_of_getElem? he)
      · cases h

/-- `step?` で動きを続けて到達した状態も `Reachable` -/
theorem Reachable.steps? {r : Rules} {decks : PlayerId → List Card} {g : State} (h : Reachable r decks g) :
    ∀ (chs : List Choice) {g' : State}, chs.foldlM (State.step? r) g = some g' → Reachable r decks g'
  | [], g', hg => by simp at hg; subst hg; exact h
  | ch :: chs, g', hg => by
    simp only [List.foldlM_cons, Option.bind_eq_bind] at hg
    cases hs : g.step? r ch with
    | none => simp [hs] at hg
    | some g1 =>
      simp only [hs, Option.bind_some] at hg
      exact (h.step (step?_sound hs)).steps? chs hg

end CardGen
