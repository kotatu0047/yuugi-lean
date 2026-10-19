import CardGen.Explore

/-!
# 適用の時刻つきの判定（OCG の手順）

`Negation.lean` の判定の手続きは「条件に合わないカードをどれでも1枚反転する」もので、OCG より選び方が自由である。
ここでは OCG の手順（yuugi-lean の `settleOnce`）に合わせて、カードごとに**適用の時刻**を持たせる。

- `y` が `x` を無効にし、`x` も `y` を無効にするときは、**先に適用された方が勝つ**（`beats`）
- 適用中のカードに負けている有効なカードがあれば、それを無効にする（どれからでもよい）
- なければ、有効に戻せるカード（無効で、どの適用中のカードにも負けていない）を1枚、新しい時刻で有効に戻す。
  何も無効にしないカードを先に戻す。ほかは ② ターンプレイヤーのカードを先に、① 同じプレイヤーのカードが
  複数あればそのプレイヤーが選ぶ
- どちらもなければ止まる

適用の時刻は大小関係しか判定に効かないので、状態では時刻の代わりに「カードの番号を時刻の古い順に並べた列」
（`order`）を持つ。有効に戻したカードは列の最後に移る。こうすると状態は有限個（有効・無効 `2^n` 通り × 並べ方 `n!` 通り）
になり、すべての状態から総当たりで調べられる。これが yuugi-lean の `quad_allEnd_any`（4すくみについて、互いに
異なるどんな時刻からでも判定が止まる）を、任意のカードの組に一般化したものになる。

**メタ定理2**（`TSys.allEnd_of_certOK`）：総当たりが「どう選んでも止まり、結果は1通り」と判断したときは、
各状態に「止まるまでの残りの歩数の上限」（`pot`）を付けた証明書を出す。証明書の検査（`certOK`）が通れば、
**どの有効・無効と適用の順番から、どう選んで進めても、判定は止まり、結果は `target` になる**（`TAllEnd`）。
-/

namespace CardGen

/-! ## 順列 -/

/-- `a` を `l` のどこか1か所に入れた列すべて -/
def insertAll {α} (a : α) : List α → List (List α)
  | [] => [[a]]
  | b :: l => (a :: b :: l) :: (insertAll a l).map (b :: ·)

/-- `l` の並べ替えすべて -/
def perms {α} : List α → List (List α)
  | [] => [[]]
  | a :: l => (perms l).flatMap (insertAll a)

theorem mem_insertAll {α} (a : α) : ∀ (s t : List α), s ++ a :: t ∈ insertAll a (s ++ t)
  | [], t => by cases t <;> simp [insertAll]
  | b :: s, t => by
    simp only [List.cons_append, insertAll, List.mem_cons, List.mem_map]
    exact .inr ⟨_, mem_insertAll a s t, rfl⟩

/-- **並べ替えはすべて `perms` にある** -/
theorem mem_perms {α} [DecidableEq α] : ∀ (l l' : List α), l'.Perm l → l' ∈ perms l
  | [], l', h => by simp [List.Perm.eq_nil h, perms]
  | a :: l, l', h => by
    obtain ⟨s, t, rfl⟩ := List.append_of_mem (h.symm.subset List.mem_cons_self)
    have h' : (s ++ t).Perm l := (List.perm_middle.symm.trans h).cons_inv
    simp only [perms, List.mem_flatMap]
    exact ⟨s ++ t, mem_perms l _ h', mem_insertAll a s t⟩

/-- 長さ `n` の真偽の列すべて -/
def allBools : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (allBools n).flatMap fun l => [false :: l, true :: l]

theorem mem_allBools : ∀ (l : List Bool), l ∈ allBools l.length
  | [] => by simp [allBools]
  | b :: l => by
    simp only [List.length_cons, allBools, List.mem_flatMap]
    exact ⟨l, mem_allBools l, by cases b <;> simp⟩

/-! ## 時刻つきの判定 -/

/-- 判定の途中の状態：カードごとの有効・無効と、カードの番号を適用の時刻の古い順に並べた列 -/
structure TState where
  on : List Bool
  order : List Nat
deriving Repr, DecidableEq, BEq, Hashable, Inhabited

/-- 無効の関係とカードのコントローラー -/
structure TSys where
  n : Nat
  rel : Nat → Nat → Bool
  ctrl : Nat → Bool

def TState.isOn (s : TState) (i : Nat) : Bool := s.on.getD i false

/-- 適用の時刻（小さいほど古い） -/
def TState.time (s : TState) (i : Nat) : Nat := s.order.idxOf i

def TState.kill (s : TState) (i : Nat) : TState := { s with on := s.on.set i false }

def TState.revive (s : TState) (i : Nat) : TState := ⟨s.on.set i true, s.order.erase i ++ [i]⟩

namespace TSys
variable (S : TSys)

/-- `y` が `x` に勝つ：`y` は `x` を無効にし、`x` が `y` を無効にして先に適用されている、ということはない -/
def beats (s : TState) (y x : Nat) : Bool := S.rel y x && !(S.rel x y && decide (s.time x < s.time y))

/-- `x` が、適用中のカードのどれかに負けている -/
def beaten (s : TState) (x : Nat) : Bool := (List.range S.n).any fun y => s.isOn y && S.beats s y x

/-- 何も無効にしないカード -/
def inert (j : Nat) : Bool := !(List.range S.n).any fun x => S.rel j x

/-- 有効に戻すカードの候補（`tp` はターンプレイヤー） -/
def cands (s : TState) (tp : Bool) : List Nat :=
  let all := (List.range S.n).filter fun j => !s.isOn j && !S.beaten s j
  match all.find? S.inert with
  | some j => [j]
  | none =>
    let mine := all.filter (S.ctrl · == tp)
    if mine.isEmpty then all else mine

/-- 判定の1歩で進める先（空なら止まる）。負けている有効なカードがあれば、どれかを無効にする。
なければ候補のどれかを有効に戻す（候補が1枚なら自動、2枚以上ならプレイヤーが選ぶ） -/
def succ (tp : Bool) (s : TState) : List TState :=
  let losing := (List.range S.n).filter fun i => s.isOn i && S.beaten s i
  if losing.isEmpty then (S.cands s tp).map s.revive else losing.map s.kill

/-- 意味のある状態：カードの枚数分の有効・無効と、カードの番号の並べ替え -/
def Valid (s : TState) : Prop := s.on.length = S.n ∧ s.order.Perm (List.range S.n)

/-- 意味のある状態すべて -/
def allStates : List TState :=
  (allBools S.n).flatMap fun on => (perms (List.range S.n)).map (⟨on, ·⟩)

theorem mem_allStates {s : TState} (h : S.Valid s) : s ∈ S.allStates := by
  simp only [allStates, List.mem_flatMap, List.mem_map]
  exact ⟨s.on, h.1 ▸ mem_allBools s.on, s.order, mem_perms _ _ h.2, rfl⟩

theorem cands_lt {s : TState} {tp : Bool} {i : Nat} (h : i ∈ S.cands s tp) : i < S.n := by
  have hall : ∀ j ∈ (List.range S.n).filter (fun j => !s.isOn j && !S.beaten s j), j < S.n :=
    fun j hj => List.mem_range.1 (List.mem_filter.1 hj).1
  simp only [cands] at h
  split at h
  · rename_i j hj
    simp only [List.mem_singleton] at h; subst h
    exact hall _ (List.mem_of_find?_eq_some hj)
  · split at h
    · exact hall _ h
    · exact hall _ (List.mem_filter.1 h).1

theorem valid_succ {tp : Bool} {s s' : TState} (hv : S.Valid s) (h : s' ∈ S.succ tp s) : S.Valid s' := by
  simp only [succ] at h
  split at h
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 h
    have hi' : i < S.n := S.cands_lt hi
    refine ⟨by simp [TState.revive, hv.1], ?_⟩
    have hmem : i ∈ s.order := hv.2.symm.subset (List.mem_range.2 hi')
    exact (List.perm_append_singleton i _).trans ((List.perm_cons_erase hmem).symm.trans hv.2)
  · obtain ⟨i, -, rfl⟩ := List.mem_map.1 h
    exact ⟨by simp [TState.kill, hv.1], hv.2⟩

/-- どう選んで進めても止まり、止まったときの有効・無効は `target`（yuugi-lean の `AllEnd` にあたる） -/
inductive TAllEnd (tp : Bool) (target : List Bool) : TState → Prop
  | halt {s : TState} : S.succ tp s = [] → s.on = target → TAllEnd tp target s
  | step {s : TState} : S.succ tp s ≠ [] → (∀ s' ∈ S.succ tp s, TAllEnd tp target s') → TAllEnd tp target s

/-- 証明書の検査。`pot` は止まるまでの残りの歩数の上限、`res` は各状態から進めたときの結果。
止まる状態では結果はその状態の有効・無効で、進める状態では進めた先の `pot` がどれも小さく、結果は同じ -/
def certOK (tp : Bool) (pot : TState → Nat) (res : TState → List Bool) : Bool :=
  S.allStates.all fun s =>
    let ss := S.succ tp s
    if ss.isEmpty then s.on == res s else ss.all fun s' => decide (pot s' < pot s) && res s' == res s

/-- **メタ定理2**：証明書の検査が通れば、意味のあるどの状態 `s` から、どう選んで進めても、
判定は止まり、結果は `res s` になる（結果は、開始時の有効・無効と適用の順番だけで決まり、選び方によらない） -/
theorem allEnd_of_certOK {tp : Bool} {pot : TState → Nat} {res : TState → List Bool}
    (hc : S.certOK tp pot res = true) : ∀ s, S.Valid s → S.TAllEnd tp (res s) s := by
  have key : ∀ m s, pot s < m → S.Valid s → S.TAllEnd tp (res s) s := by
    intro m
    induction m with
    | zero => intro s h; exact absurd h (Nat.not_lt_zero _)
    | succ m ih =>
      intro s hm hv
      have hs := List.all_eq_true.1 hc s (S.mem_allStates hv)
      by_cases he : (S.succ tp s).isEmpty
      · simp only [he, ite_true, beq_iff_eq] at hs
        exact .halt (List.isEmpty_iff.1 he) hs
      · simp only [he] at hs
        refine .step (fun h => he (List.isEmpty_iff.2 h)) fun s' hs' => ?_
        have h2 := List.all_eq_true.1 hs s' hs'
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h2
        rw [← h2.2]
        exact ih s' (by omega) (S.valid_succ hv hs')
  exact fun s hv => key (pot s + 1) s (Nat.lt_succ_self _) hv

/-- 結果が1通り：どの状態から始めても結果が `target` -/
theorem allEnd_const {tp : Bool} {pot : TState → Nat} {target : List Bool}
    (hc : S.certOK tp pot (fun _ => target) = true) : ∀ s, S.Valid s → S.TAllEnd tp target s :=
  S.allEnd_of_certOK hc

end TSys

/-! ## 盤面から作る -/

/-- 盤面から作る。無効の関係（`instRel`）は最初に表にしておく（判定の1歩ごとに範囲の指定を調べ直さない） -/
def TSys.ofInsts (insts : List Inst) : TSys :=
  let n := insts.length
  let table : Array (Array Bool) := (List.range n).toArray.map fun y => (List.range n).toArray.map fun x => instRel insts y x
  ⟨n, fun y x => (table[y]?.bind (·[x]?)).getD false, fun i => (insts[i]?.map (·.controller)).getD true⟩

/-- 時刻つきの判定の総当たりの分類（下ほど悪い） -/
inductive TVerdict
  /-- どの状態から、どう選んでも止まり、結果は1通り -/
  | unique
  /-- どの状態から、どう選んでも止まり、結果は開始時の状態（適用された順番など）だけで決まる -/
  | byHistory
  /-- 止まるが、選び方によって結果が変わる状態がある -/
  | choiceResult
  /-- 選び方によって回り続ける状態がある（止まる選び方はある） -/
  | someLoop
  /-- どう選んでも止まらない状態がある -/
  | cannotHalt
  /-- 止まる状態がない -/
  | noStable
deriving Repr, DecidableEq, BEq

def TVerdict.severity : TVerdict → Nat
  | .unique => 0 | .byHistory => 1 | .choiceResult => 2 | .someLoop => 3 | .cannotHalt => 4 | .noStable => 5

/-- 時刻つきの判定の総当たりの結果 -/
structure TimedResult where
  verdict : TVerdict
  /-- `unique`・`byHistory` のとき、証明書（状態ごとの残りの歩数の上限と結果） -/
  pot : Std.HashMap TState Nat
  res : Std.HashMap TState (List Bool)

/-- すべての状態について、進め方を調べる -/
def TSys.analyze (S : TSys) (tp : Bool) : TimedResult := Id.run do
  let states := S.allStates.toArray
  let N := states.size
  let index : Std.HashMap TState Nat := states.foldl (init := {}) fun (m : Std.HashMap TState Nat) s => m.insert s m.size
  let succs : Array (List Nat) := states.map fun s => (S.succ tp s).filterMap index.get?
  let halting : Array Bool := succs.map (·.isEmpty)
  let fail (v : TVerdict) : TimedResult := ⟨v, {}, {}⟩
  if !halting.any id then return fail .noStable
  let mut canHalt := halting
  let mut changed := true
  while changed do
    changed := false
    for s in [0:N] do
      if !canHalt[s]! && (succs[s]!).any (canHalt[·]!) then
        canHalt := canHalt.set! s true
        changed := true
  if canHalt.any (!·) then return fail .cannotHalt
  -- どう選んでも止まる状態に、回ごとに印を付ける。印を付けた回を残りの歩数の上限に、
  -- 進めた先の結果がどれも同じならそれを結果にする（違えば `none`）
  let mut pot : Array Nat := Array.replicate N 0
  let mut res : Array (Option (List Bool)) := (List.range N).toArray.map fun i =>
    if halting[i]! then some (states[i]!).on else none
  let mut conflict := false
  let mut allHalt := halting
  let mut round := 0
  changed := true
  while changed do
    changed := false
    round := round + 1
    let prev := allHalt
    let prevRes := res
    for s in [0:N] do
      if !prev[s]! && (succs[s]!).all (prev[·]!) then
        allHalt := allHalt.set! s true
        pot := pot.set! s round
        let rs := (succs[s]!).map (prevRes[·]!)
        let r := rs.head!
        if rs.all (· == r) && r.isSome then res := res.set! s r else conflict := true
        changed := true
  if allHalt.any (!·) then return fail .someLoop
  if conflict then return fail .choiceResult
  let rs := res.toList.filterMap id
  let potMap := (List.range N).foldl (init := ({} : Std.HashMap TState Nat)) fun m i => m.insert states[i]! pot[i]!
  let resMap := (List.range N).foldl (init := ({} : Std.HashMap TState (List Bool))) fun m i =>
    m.insert states[i]! (res[i]!).get!
  return ⟨if rs.eraseDups.length == 1 then .unique else .byHistory, potMap, resMap⟩

/-- 証明書の検査（`certOK`）を通したか。通れば `TSys.allEnd_of_certOK` により、どう選んでも止まり、
結果は開始時の状態だけで決まる -/
def TSys.certified (S : TSys) (tp : Bool) (r : TimedResult) : Bool :=
  (r.verdict == .unique || r.verdict == .byHistory) && S.certOK tp (r.pot.getD · 0) (r.res.getD · [])

/-! ## まとまりの盤面の総当たり -/

/-- 1人分のカードを、フィールド上のゾーンに容量を守って置けるか -/
def fitsZones (r : Rules) (cs : List Card) : Bool :=
  let caps : List (List TypeName × Nat) := r.zones.filterMap fun z =>
    if z.role == .plain && z.onField then
      some (z.admits, if z.capacity == .one then z.count else cs.length)
    else none
  let rec go (caps : List (List TypeName × Nat)) : List Card → Bool
    | [] => true
    | c :: rest => (List.range caps.length).any fun i =>
        match caps[i]? with
        | some (ad, k) => ad.contains c.type && k > 0 && go (caps.set i (ad, k - 1)) rest
        | none => false
  go caps cs

/-- 1枚のカードを1人あたり置く最大の枚数 -/
def maxCopies : Nat := 2

/-- 総当たりする盤面の最大の枚数（反転の手続き） -/
def boardLimit : Nat := 5

/-- 時刻つきの判定で調べる盤面の最大の枚数（状態は `2^n × n!` 通りあるので小さくする） -/
def timedLimit : Nat := 5

/-- まとまりの各カードを自分・相手にそれぞれ 0〜`maxCopies` 枚置いた盤面（すべて表側表示）のうち、
枚数が `boardLimit` 以下で、ゾーンの容量を守って置けるもの（空の盤面は除く） -/
def boardsFor (r : Rules) (group : List Card) : List (List Inst) :=
  let counts := group.foldr (fun _ acc => acc.flatMap fun l =>
    (List.range (maxCopies + 1)).flatMap fun a => (List.range (maxCopies + 1)).map fun b => (a, b) :: l) [[]]
  let ok := counts.filter fun l =>
    let total := (l.map fun (a, b) => a + b).sum
    total > 0 && total ≤ boardLimit
  ok.filterMap fun l =>
    let side (mine : Bool) : List Card := (group.zip l).flatMap fun (c, a, b) =>
      List.replicate (if mine then a else b) c
    if fitsZones r (side true) && fitsZones r (side false) then
      -- 位置は考えない（マスの関係を使う無効は当たらないものとして調べる。報告にその旨を書く）
      some ((side true).map (⟨·, true, true, none⟩) ++ (side false).map (⟨·, false, true, none⟩))
    else none

/-- 総当たりする、まとまりのカードの最大の枚数 -/
def exploreLimit : Nat := 4

structure GroupResult where
  cards : List String
  /-- 調べた盤面の数（0 ならカードが多すぎて調べていない） -/
  boards : Nat
  /-- 反転の手続き（`Negation.lean`）で一番悪い分類と、その盤面 -/
  verdict : Verdict
  board : List (String × Bool)
  /-- 時刻つきの判定（OCG の手順）で一番悪い分類と、その盤面とターンプレイヤー -/
  timed : TVerdict
  timedBoard : List (String × Bool)
  timedTurn : Bool
  /-- 止まると判断した盤面がすべて証明書の検査（`certOK`）を通った -/
  certified : Bool
deriving Repr

def boardNames (b : List Inst) : List (String × Bool) := b.map fun i => (i.card.name, i.controller)

/-- まとまりについて、一番悪い分類の盤面を探す（大きすぎれば調べない） -/
def exploreGroup (r : Rules) (group : List Card) : GroupResult :=
  let names := group.map (·.name)
  if group.length > exploreLimit then ⟨names, 0, .ok, [], .unique, [], true, true⟩
  else
    let boards := boardsFor r group
    boards.foldl (fun (acc : GroupResult) b =>
      let v := analyzeBoard b
      let acc := if v.severity > acc.verdict.severity then { acc with verdict := v, board := boardNames b } else acc
      let S := TSys.ofInsts b
      -- 盤面の集まりは自分と相手を入れ替えても同じなので、ターンプレイヤーは自分だけ調べればよい
      if b.length > timedLimit then acc else
      [true].foldl (fun (acc : GroupResult) tp =>
        let res := S.analyze tp
        let cert := match res.verdict with
          | .unique | .byHistory => S.certified tp res
          | _ => true
        let acc := { acc with certified := acc.certified && cert }
        if res.verdict.severity > acc.timed.severity then
          { acc with timed := res.verdict, timedBoard := boardNames b, timedTurn := tp }
        else acc) acc)
      ⟨names, boards.length, .ok, [], .unique, [], true, true⟩

end CardGen
