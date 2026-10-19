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
  /-- `p` が手札の `hand` 番目のカードを `zone` 番目のゾーンの `cell` 番目のマスに置く（`up`：表側表示か） -/
  | place (p : PlayerId) (hand : Nat) (zone : Nat) (cell : Nat) (up : Bool)
  /-- `p` がフィールドの `k` 番目のカードの `eff` 番目の効果を発動して解決する（`apply`：無効にされていないか。
  `neg`：効果が無効になっているカードの位置。守備力の計算に使う） -/
  | resolve (p : PlayerId) (k : Nat) (eff : Nat) (apply : Bool) (neg : List Pos := []) (tgt : Option Pos := none)
  /-- `p` がフィールドの `k` 番目のカードで、相手のフィールドの `target` 番目のカード（`none` なら直接）を攻撃する。
  `neg`：効果が無効になっているカードの位置（攻撃力の計算に使う） -/
  | attack (p : PlayerId) (k : Nat) (target : Option Nat) (neg : List Pos)
  /-- MTG 式の戦闘：`p` のフィールドの `atk` 番目のカードたちで攻撃し、相手のフィールドの `j` 番目のカードが
  `atk` の `a` 番目の攻撃をブロックする（`blocks` の `(j, a)`） -/
  | combat (p : PlayerId) (atk : List Nat) (blocks : List (Nat × Nat)) (neg : List Pos)
  /-- どのカードのダメージも 0 に戻す -/
  | mend
  /-- 状態の確認（守備力以上のダメージを受けている戦闘できるカードを破壊する） -/
  | settle (neg : List Pos)
  /-- `p` が手札の `hand` 番目のカードを墓地へ捨てる -/
  | discard (p : PlayerId) (hand : Nat)
deriving Repr, DecidableEq

/-- 攻撃の対象として選べるか（`none` は直接攻撃：相手に戦闘できるカードがないとき） -/
def State.targetOK (r : Rules) (g : State) (p : PlayerId) : Option Nat → Bool
  | none => r.blocking || (g (!p)).field.all (!r.fights ·)
  | some j => ((g (!p)).field[j]?.map r.fights).getD false

/-- `p` の `i` 番目のゾーンの、空いている最初のマス（なければ 0。「何枚でも」のゾーンなら 0） -/
def State.freeCell (r : Rules) (g : State) (p : PlayerId) (i : Nat) : Nat :=
  match r.zones[i]? with
  | some z =>
    if z.capacity == .one then
      ((List.range z.count).find? fun j => (g p).field.all fun sl => !(sl.zone == i && sl.cell == j)).getD 0
    else 0
  | none => 0

/-- 選んだ動きをしたあとの状態（できない動きなら `none`）。計算済みの値にする前のもの -/
def State.step0? (r : Rules) (g : State) : Choice → Option State
  | .draw p =>
    match (g p).deck with
    | c :: d => some (g.set p { g p with deck := d, hand := (g p).hand ++ [c] })
    | [] => none
  | .place p h i j up => do
    let c ← (g p).hand[h]?
    let z ← r.zones[i]?
    guard (z.role == .plain && z.admits.contains c.type && decide (j < z.count) &&
      (z.capacity != .one || (g p).field.all (fun sl => !(sl.zone == i && sl.cell == j))))
    return g.set p { g p with hand := (g p).hand.erase c, field := (g p).field ++ [⟨i, j, c, up, 0, 0, 0⟩] }
  | .resolve p k e apply neg tgt => do
    let sl ← (g p).field[k]?
    match sl.card.effects[e]? with
    | some (.activated as) => some (g.resolve r p k sl as apply neg tgt)
    | _ => none
  | .attack p k t neg => do
    let sl ← (g p).field[k]?
    guard (sl.faceUp && r.fights sl && g.targetOK r p t)
    return g.battle r neg p k sl t
  | .combat p atk blocks neg => if g.combatOK r p atk blocks then some (g.combat r neg p atk blocks) else none
  | .mend => some g.mend
  | .settle neg => some (g.sweep r neg)
  | .discard p h => do
    let c ← (g p).hand[h]?
    return g.set p { g p with hand := (g p).hand.erase c, grave := (g p).grave ++ [c] }

/-- 盤面を、2人分の計算済みの値から作り直す（値は `g` と同じ）。実行時に、前の盤面を参照する関数が積み重なって
読むたびに計算し直すことがないようにする -/
def State.fresh (g : State) : State := State.of (g true) (g false)

theorem State.fresh_eq (g : State) : g.fresh = g := by
  funext q; cases q <;> rfl

/-- 選んだ動きをしたあとの状態（できない動きなら `none`） -/
def State.step? (r : Rules) (g : State) (ch : Choice) : Option State :=
  match g.step0? r ch with
  | some g' => some (State.of (g' true) (g' false))
  | none => none

theorem step0?_sound {r : Rules} {g g' : State} {ch : Choice} (h : g.step0? r ch = some g') : Step r g g' := by
  cases ch with
  | draw p =>
    simp only [State.step0?] at h
    split at h
    · rename_i c d hd; cases h; exact .draw g p c d hd
    · cases h
  | place p hi i j up =>
    simp only [State.step0?, Option.bind_eq_bind] at h
    cases hc : (g p).hand[hi]? with
    | none => simp [hc] at h
    | some c =>
      cases hz : r.zones[i]? with
      | none => simp [hc, hz] at h
      | some z =>
        simp only [hc, hz, Option.bind_some] at h
        by_cases hg : (z.role == .plain && z.admits.contains c.type && decide (j < z.count) &&
            (z.capacity != .one || (g p).field.all (fun sl => !(sl.zone == i && sl.cell == j)))) = true
        · simp only [hg, guard, ite_true, Option.pure_def, Option.bind_some] at h
          cases h
          simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, bne_iff_ne, ne_eq,
            decide_eq_true_eq, List.all_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
            beq_eq_false_iff_ne] at hg
          refine .place g p c i j z up (List.mem_of_getElem? hc) hz hg.1.1.1 hg.1.1.2 hg.1.2 fun hcap => ?_
          rcases hg.2 with h1 | h1
          · exact absurd hcap h1
          · intro sl hm ⟨h2, h3⟩
            rcases h1 sl hm with h4 | h4
            · exact h4 h2
            · exact h4 h3
        · rw [Bool.not_eq_true] at hg
          simp only [hg, guard] at h
          cases h
  | resolve p k e apply neg tgt =>
    simp only [State.step0?, Option.bind_eq_bind] at h
    cases hk : (g p).field[k]? with
    | none => simp [hk] at h
    | some sl =>
      simp only [hk, Option.bind_some] at h
      split at h
      · rename_i as he
        cases h
        exact .resolve g p k sl as apply neg tgt hk (List.mem_of_getElem? he)
      · cases h
  | attack p k t neg =>
    simp only [State.step0?, Option.bind_eq_bind] at h
    cases hk : (g p).field[k]? with
    | none => simp [hk] at h
    | some sl =>
      simp only [hk, Option.bind_some] at h
      by_cases hg : (sl.faceUp && r.fights sl && g.targetOK r p t) = true
      · simp only [hg, guard, ite_true, Option.pure_def, Option.bind_some] at h
        cases h
        simp only [Bool.and_eq_true] at hg
        refine .attack g p k sl t neg hk hg.1.1 hg.1.2 ?_
        cases t with
        | none => simpa [State.targetOK] using hg.2
        | some j =>
          have h2 := hg.2
          simp only [State.targetOK] at h2
          cases hj : (g (!p)).field[j]? with
          | none => simp [hj] at h2
          | some tl => simp only [hj, Option.map_some, Option.getD_some] at h2; exact ⟨tl, hj, h2⟩
      · rw [Bool.not_eq_true] at hg
        simp only [hg, guard] at h
        cases h
  | combat p atk blocks neg =>
    simp only [State.step0?] at h
    split at h
    · rename_i hok; cases h; exact .combat g p atk blocks neg hok
    · cases h
  | mend =>
    simp only [State.step0?, Option.some.injEq] at h
    subst h; exact .mend g
  | settle neg =>
    simp only [State.step0?, Option.some.injEq] at h
    subst h; exact .settle g neg
  | discard p hi =>
    simp only [State.step0?, Option.bind_eq_bind] at h
    cases hc : (g p).hand[hi]? with
    | none => simp [hc] at h
    | some c =>
      simp only [hc, Option.bind_some, Option.pure_def, Option.some.injEq] at h
      subst h; exact .discard g p c (List.mem_of_getElem? hc)

/-- **`step?` で進めた状態は、`Step` で進めた状態** -/
theorem step?_sound {r : Rules} {g g' : State} {ch : Choice} (h : g.step? r ch = some g') : Step r g g' := by
  unfold State.step? at h
  split at h
  · rename_i g0 h0
    cases h
    have : State.of (g0 true) (g0 false) = g0 := State.fresh_eq g0
    rw [this]
    exact step0?_sound h0
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
