import CardGen.Play
import CardGen.Pool

/-!
# ターン

`Step`（`Model.lean`）は、どちらのプレイヤーもいつでも何度でも動ける、実際の対戦より自由なモデルである。
ここではその上に**ターン**を重ねる。状態は盤面（`State`）とターンの情報（`TurnInfo`）の組（`Match`）で、
実行できる1歩 `Match.step?` で進める。

- カードを置く・攻撃するのはターンプレイヤーだけ。場のカードの発動はどちらのプレイヤーもいつでもできる
- 戦闘できる種類のカードを置くのは、1ターンに `Rules.summonsPerTurn` 枚まで（通常召喚。0 なら制限なし）
- 戦闘できるカードの攻撃は、1ターンに1枚1回まで。先攻の最初のターンは `Rules.firstTurnAttack` のときだけ攻撃できる
- 「ターン終了」で相手のターンになり、新しいターンプレイヤーが `Rules.drawPerTurn` 枚引く
  （デッキが足りなければある分だけ）。先攻の最初のターンは `Rules.firstTurnDraw` のときだけ引く
- 自由に引く動きはない（引くのはターンの最初と、効果によるときだけ）
- マナ：ターンプレイヤーは、表側表示の「フィールド上」の、マナを出すカード（`Card.mana`）をタップして、
  その色（`Card.manaColor`。`""` は無色）のマナを得る。カードを置くには、どのマナで払うか（`pay`）を選ぶ。
  払うマナは持っているマナの一部で、色の決まったコスト（`Card.colorCost`）を含み、全部でコストの合計
  （`Card.cost` ＋ 色の決まったコストの数）だけ。マナはターンの終わりに消える
- タップしたカードは、持ち主の次のターンの始めに起きる（アンタップ）。`Rules.attackTaps` なら攻撃でもタップし、
  タップしているカードは攻撃できない
- 種類ごとに、1ターンに置ける枚数の上限（`Rules.placeLimits`。例：土地は1ターンに1枚）
- `Rules.summoningSickness` なら、置いたターンの戦闘できるカードは攻撃もタップもできない（召喚酔い）

**ターンのある対戦の盤面は、どれもターンのないモデルで到達できる盤面**（`TReachable.reachable`）。
1歩はどれも `Step` の0回以上の繰り返しになるからである。そのため、盤面の制約（`Reachable.inv`）、
★（`derived_valid`・`gameClaims_valid`）、受け入れた証明のジョブは、ターンのある対戦でもそのまま成り立つ
（`TReachable.of_reachable`）。そのうえで、ターンがあるから言える性質（`TReachable.summons_le` など）を示す。
-/

namespace CardGen

/-- 攻撃したカードの記録を、今のフィールドにあるものだけに絞る。同じカードが複数あれば、フィールドにある枚数まで残す -/
def prune : List Slot → List Slot → List Slot
  | [], _ => []
  | a :: as, f => if a ∈ f then a :: prune as (f.erase a) else prune as f

/-- `l` の各カードの枚数が、`f` の枚数以下（`l` は `f` の一部を取り出したもの） -/
def BagLe (l f : List Slot) : Prop := ∀ a, l.count a ≤ f.count a

theorem prune_bagLe : ∀ (as f : List Slot), BagLe (prune as f) f
  | [], f => by intro a; simp [prune]
  | x :: as, f => by
    intro a
    unfold prune
    split
    · rename_i hx
      have ih := prune_bagLe as (f.erase x) a
      rw [List.count_erase] at ih
      rw [List.count_cons]
      by_cases hxa : x = a
      · subst hxa
        have := List.count_pos_iff.2 hx
        simp at ih ⊢
        omega
      · have : (x == a) = false := by simpa using hxa
        simp [this] at ih ⊢
        omega
    · exact prune_bagLe as f a

/-- ターンの情報 -/
structure TurnInfo where
  /-- ターンプレイヤー -/
  tp : PlayerId
  /-- 何ターン目か（1 から） -/
  count : Nat := 1
  /-- このターンに置いた、戦闘できる種類のカードの枚数 -/
  summons : Nat := 0
  /-- このターンに攻撃したカード（ターンプレイヤーのフィールドにあるものだけ） -/
  attacked : List Slot := []
  /-- このターンに置いたカードの種類（置いた順） -/
  placed : List TypeName := []
  /-- このターンに置いたカード（ターンプレイヤーのフィールドにあるものだけ。召喚酔いに使う） -/
  entered : List Slot := []
  /-- ターンプレイヤーのマナ（色の名前を、1マナにつき1つ並べたもの。`""` は無色）。タップで増え、カードを置くと減る。
  ターンの終わりに消える -/
  pool : List String := []
  /-- タップしている、ターンプレイヤーのカード -/
  tapped : List Slot := []
  /-- タップしている、相手のカード（相手の次のターンの始めに起きる） -/
  oppTapped : List Slot := []
  /-- ブロックを待っている攻撃（攻撃したカードの、ターンプレイヤーのフィールドの位置）。MTG 式の戦闘だけで使う -/
  pending : Option Nat := none
  /-- このターンにブロックした、相手のカード（相手のフィールドにあるものだけ） -/
  blocked : List Slot := []
deriving Repr, DecidableEq

/-- ターンのある対戦の状態 -/
structure Match where
  g : State
  turn : TurnInfo

/-- ターンのある対戦の動き -/
inductive TChoice
  /-- ターンプレイヤーが手札の `hand` 番目のカードを `zone` 番目のゾーンの `cell` 番目のマスに置く。`pay`：払うマナ -/
  | place (hand : Nat) (zone : Nat) (cell : Nat) (up : Bool) (pay : List String := [])
  /-- `p` がフィールドの `k` 番目のカードの `eff` 番目の効果を発動して解決する（どちらのターンでもよい） -/
  | resolve (p : PlayerId) (k : Nat) (eff : Nat) (apply : Bool)
  /-- ターンプレイヤーがフィールドの `k` 番目のカードで攻撃する（MTG 式の戦闘では攻撃の宣言だけで、`target` は `none`） -/
  | attack (k : Nat) (target : Option Nat) (neg : List Pos)
  /-- MTG 式の戦闘で、攻撃されたプレイヤーが、フィールドの `target` 番目のカードでブロックする（`none` ならしない） -/
  | block (target : Option Nat) (neg : List Pos)
  /-- ターンプレイヤーがフィールドの `k` 番目のカードをタップしてマナを出す -/
  | tap (k : Nat)
  /-- ターンを終え、相手のターンにする -/
  | endTurn
deriving Repr, DecidableEq

/-- `n` 枚引く（デッキが足りなければある分だけ） -/
def State.drawUpTo (r : Rules) (p : PlayerId) : Nat → State → State
  | 0, g => g
  | n + 1, g =>
    match g.step? r (.draw p) with
    | some g' => State.drawUpTo r p n g'
    | none => g

/-- 開始時の状態（`first` が先攻）。先攻の最初のターンに引くルールなら引く -/
def Match.start (r : Rules) (decks : PlayerId → List Card) (first : PlayerId) : Match :=
  ⟨if r.firstTurnDraw then (CardGen.start r decks).drawUpTo r first r.drawPerTurn else CardGen.start r decks,
   { tp := first }⟩

/-- カードの記録を、新しい盤面に合わせる（ターンプレイヤーと相手のフィールドにあるものだけにする） -/
def TurnInfo.prune (t : TurnInfo) (g : State) : TurnInfo :=
  { t with attacked := CardGen.prune t.attacked (g t.tp).field,
           entered := CardGen.prune t.entered (g t.tp).field,
           tapped := CardGen.prune t.tapped (g t.tp).field,
           oppTapped := CardGen.prune t.oppTapped (g (!t.tp)).field,
           blocked := CardGen.prune t.blocked (g (!t.tp)).field }

/-- 記録 `l` にない（同じカードのうち、記録にない1枚がフィールドにある） -/
def notIn (l field : List Slot) (sl : Slot) : Bool := decide (l.count sl < field.count sl)

/-- `l` の各要素の個数が、`m` の個数以下（多重集合として含まれる） -/
def bagLeB (l m : List String) : Bool := l.all fun a => decide (l.count a ≤ m.count a)

/-- マナ `pay` でカード `c` のコストを払えるか：持っているマナ `pool` の一部で、色の決まったコストを含み、全部でコストの合計 -/
def payOK (c : Card) (pool pay : List String) : Bool :=
  bagLeB pay pool && bagLeB c.colorCost pay && pay.length == c.cost + c.colorCost.length

/-- 払い方を1つ選ぶ（テストプレイの既定の払い方）：色の決まったコストはその色で払い、残りは無色のマナから先に、
次に持っている順に払う。払えなければ `none`。どの払い方も `payOK` を満たす（`autoPay_ok`） -/
def autoPay (c : Card) (pool : List String) : Option (List String) :=
  let rest := c.colorCost.foldl List.erase pool
  let generic := rest.filter (· == "") ++ rest.filter (· != "")
  let pay := c.colorCost ++ generic.take c.cost
  if payOK c pool pay then some pay else none

theorem autoPay_ok {c : Card} {pool pay : List String} (h : autoPay c pool = some pay) : payOK c pool pay = true := by
  simp only [autoPay] at h
  split at h
  · cases h; assumption
  · cases h

/-- このターンに、カード `sl` を、マナ `pay` で払って置けるか（召喚の上限・種類ごとの上限・マナ） -/
def TurnInfo.placeOK (r : Rules) (t : TurnInfo) (sl : Slot) (pay : List String) : Bool :=
  (!r.fights sl || r.summonsPerTurn == 0 || decide (t.summons < r.summonsPerTurn)) &&
  r.placeLimits.all (fun l => !l.types.contains sl.card.type ||
    decide ((t.placed.filter l.types.contains).length < l.count)) &&
  payOK sl.card t.pool pay

/-- カード `sl` を、マナ `pay` で払って置いたあとのターンの情報 -/
def TurnInfo.afterPlace (r : Rules) (t : TurnInfo) (sl : Slot) (pay : List String) : TurnInfo :=
  { t with summons := t.summons + (if r.fights sl then 1 else 0), placed := t.placed ++ [sl.card.type],
           entered := sl :: t.entered, pool := pay.foldl List.erase t.pool }

/-- 召喚酔いで動けないか（置いたターンの、戦闘できるカード） -/
def TurnInfo.sick (r : Rules) (t : TurnInfo) (field : List Slot) (sl : Slot) : Bool :=
  r.summoningSickness && r.fights sl && !notIn t.entered field sl

/-- フィールドのカード `sl` で、このターンに攻撃できるか -/
def TurnInfo.attackOK (r : Rules) (t : TurnInfo) (field : List Slot) (sl : Slot) : Bool :=
  (r.firstTurnAttack || t.count != 1) && notIn t.attacked field sl &&
  (!r.attackTaps || notIn t.tapped field sl) && !t.sick r field sl

/-- フィールドのカード `sl` をタップしてマナを出せるか -/
def TurnInfo.tapOK (r : Rules) (t : TurnInfo) (field : List Slot) (sl : Slot) : Bool :=
  sl.faceUp && r.onFieldZone sl.zone && decide (0 < sl.card.mana) && notIn t.tapped field sl && !t.sick r field sl

/-- カード `sl` で攻撃したあとのターンの情報 -/
def TurnInfo.afterAttack (r : Rules) (t : TurnInfo) (sl : Slot) : TurnInfo :=
  { t with attacked := sl :: t.attacked, tapped := if r.attackTaps then sl :: t.tapped else t.tapped }

/-- カード `sl` をタップしてマナを出したあとのターンの情報 -/
def TurnInfo.afterTap (t : TurnInfo) (sl : Slot) : TurnInfo :=
  { t with pool := t.pool ++ List.replicate sl.card.mana sl.card.manaColor, tapped := sl :: t.tapped }

/-- ターン終了のあと、相手のターンの情報（相手のタップしていたカードは起き、自分のは残る） -/
def TurnInfo.next (t : TurnInfo) : TurnInfo := { tp := !t.tp, count := t.count + 1, oppTapped := t.tapped }

/-- 相手のフィールド `opp` の `target` 番目のカードでブロックできるか（このターンにまだブロックしておらず、
攻撃でタップするルールならタップしていない） -/
def TurnInfo.blockOK (r : Rules) (t : TurnInfo) (opp : List Slot) : Option Nat → Bool
  | none => true
  | some j =>
    match opp[j]? with
    | some tl => notIn t.blocked opp tl && (!r.attackTaps || notIn t.oppTapped opp tl)
    | none => false

/-- ブロックのあとのターンの情報 -/
def TurnInfo.afterBlock (t : TurnInfo) (opp : List Slot) (target : Option Nat) : TurnInfo :=
  { t with pending := none, blocked := (target.bind (opp[·]?)).toList ++ t.blocked }

/-- 選んだ動きをしたあとの状態（できない動きなら `none`）。ブロックを待っている間は、ブロックしかできない -/
def Match.step? (r : Rules) (m : Match) (ch : TChoice) : Option Match :=
  match m.turn.pending, ch with
  | some k, .block t neg =>
    if m.turn.blockOK r (m.g (!m.turn.tp)).field t then
      (m.g.step? r (.attack m.turn.tp k t neg)).map fun g =>
        ⟨g, (m.turn.afterBlock (m.g (!m.turn.tp)).field t).prune g⟩
    else none
  | some _, _ => none
  | none, ch => step0? r m ch
where
  /-- ブロックを待っていないときの1歩 -/
  step0? (r : Rules) (m : Match) : TChoice → Option Match
  | .block _ _ => none
  | .place h i j up pay =>
    match (m.g m.turn.tp).hand[h]? with
    | none => none
    | some c =>
      if m.turn.placeOK r ⟨i, j, c, up⟩ pay then
        (m.g.step? r (.place m.turn.tp h i j up)).map fun g => ⟨g, (m.turn.afterPlace r ⟨i, j, c, up⟩ pay).prune g⟩
      else none
  | .resolve p k e apply =>
    (m.g.step? r (.resolve p k e apply)).map fun g => ⟨g, m.turn.prune g⟩
  | .attack k t neg =>
    match (m.g m.turn.tp).field[k]? with
    | none => none
    | some sl =>
      if m.turn.attackOK r (m.g m.turn.tp).field sl then
        if r.blocking then
          -- 攻撃の宣言：相手がブロックを選ぶまで待つ
          if sl.faceUp && r.fights sl && t.isNone then
            some ⟨m.g, { m.turn.afterAttack r sl with pending := some k }.prune m.g⟩
          else none
        else (m.g.step? r (.attack m.turn.tp k t neg)).map fun g => ⟨g, (m.turn.afterAttack r sl).prune g⟩
      else none
  | .tap k =>
    match (m.g m.turn.tp).field[k]? with
    | none => none
    | some sl =>
      if m.turn.tapOK r (m.g m.turn.tp).field sl then
        some ⟨m.g, (m.turn.afterTap sl).prune m.g⟩
      else none
  | .endTurn =>
    let g := m.g.drawUpTo r (!m.turn.tp) r.drawPerTurn
    some ⟨g, m.turn.next.prune g⟩

/-- 開始時の状態から、`step?` を繰り返して到達できる -/
inductive TReachable (r : Rules) (decks : PlayerId → List Card) (first : PlayerId) : Match → Prop
  | start : TReachable r decks first (Match.start r decks first)
  | step {m m'} (ch : TChoice) : TReachable r decks first m → m.step? r ch = some m' → TReachable r decks first m'

/-! ## 1歩の中身 -/

/-- 1歩のあとの盤面は、ターンのないモデルで、もとの盤面から到達できる盤面（`Step` の0回以上の繰り返し）。
ターンの情報は、ある記録をその盤面に合わせたもの -/
inductive Match.Moved (r : Rules) (m : Match) : TChoice → Match → Prop
  | place {h i j up pay c g} : (m.g m.turn.tp).hand[h]? = some c → m.turn.placeOK r ⟨i, j, c, up⟩ pay →
      m.g.step? r (.place m.turn.tp h i j up) = some g →
      Match.Moved r m (.place h i j up pay) ⟨g, (m.turn.afterPlace r ⟨i, j, c, up⟩ pay).prune g⟩
  | resolve {p k e apply g} : m.g.step? r (.resolve p k e apply) = some g →
      Match.Moved r m (.resolve p k e apply) ⟨g, m.turn.prune g⟩
  | declare {k t neg sl} : (m.g m.turn.tp).field[k]? = some sl →
      Match.Moved r m (.attack k t neg) ⟨m.g, { m.turn.afterAttack r sl with pending := some k }.prune m.g⟩
  | block {k t neg g} : m.turn.pending = some k → m.g.step? r (.attack m.turn.tp k t neg) = some g →
      Match.Moved r m (.block t neg) ⟨g, (m.turn.afterBlock (m.g (!m.turn.tp)).field t).prune g⟩
  | attack {k t neg sl g} : (m.g m.turn.tp).field[k]? = some sl →
      m.g.step? r (.attack m.turn.tp k t neg) = some g →
      Match.Moved r m (.attack k t neg) ⟨g, (m.turn.afterAttack r sl).prune g⟩
  | tap {k sl} : (m.g m.turn.tp).field[k]? = some sl →
      Match.Moved r m (.tap k) ⟨m.g, (m.turn.afterTap sl).prune m.g⟩
  | endTurn : Match.Moved r m .endTurn
      ⟨m.g.drawUpTo r (!m.turn.tp) r.drawPerTurn, m.turn.next.prune (m.g.drawUpTo r (!m.turn.tp) r.drawPerTurn)⟩

theorem Match.step0?_moved {r : Rules} {m m' : Match} {ch : TChoice} (hs : Match.step?.step0? r m ch = some m') :
    Match.Moved r m ch m' := by
  cases ch with
  | block t neg => simp [Match.step?.step0?] at hs
  | place h i j up pay =>
    simp only [Match.step?.step0?] at hs
    split at hs
    · cases hs
    · rename_i c hc
      split at hs
      · rename_i hok
        obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.1 hs
        exact .place hc hok hg
      · cases hs
  | resolve p k e apply =>
    simp only [Match.step?.step0?] at hs
    obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.1 hs
    exact .resolve hg
  | attack k t neg =>
    simp only [Match.step?.step0?] at hs
    split at hs
    · cases hs
    · rename_i sl hsl
      split at hs
      · split at hs
        · split at hs
          · cases hs; exact .declare hsl
          · cases hs
        · obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.1 hs
          exact .attack hsl hg
      · cases hs
  | tap k =>
    simp only [Match.step?.step0?] at hs
    split at hs
    · cases hs
    · rename_i sl hsl
      split at hs
      · cases hs; exact .tap hsl
      · cases hs
  | endTurn =>
    simp only [Match.step?.step0?, Option.some.injEq] at hs
    subst hs
    exact .endTurn

theorem Match.step?_moved {r : Rules} {m m' : Match} {ch : TChoice} (hs : m.step? r ch = some m') :
    Match.Moved r m ch m' := by
  unfold Match.step? at hs
  split at hs
  · rename_i k t neg hk
    split at hs
    · obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.1 hs
      exact .block hk hg
    · cases hs
  · cases hs
  · exact Match.step0?_moved hs

/-! ## ターンのない対戦への引き継ぎ -/

theorem Reachable.drawUpTo {r : Rules} {decks : PlayerId → List Card} (p : PlayerId) :
    ∀ (n : Nat) {g : State}, Reachable r decks g → Reachable r decks (g.drawUpTo r p n)
  | 0, _, h => h
  | n + 1, g, h => by
    unfold State.drawUpTo
    split
    · rename_i g' hg
      exact Reachable.drawUpTo p n (h.step (step?_sound hg))
    · exact h

/-- **ターンのある対戦の盤面は、どれもターンのないモデルで到達できる盤面** -/
theorem TReachable.reachable {r : Rules} {decks : PlayerId → List Card} {first : PlayerId} {m : Match}
    (h : TReachable r decks first m) : Reachable r decks m.g := by
  induction h with
  | start =>
    simp only [Match.start]
    split
    · exact Reachable.drawUpTo first _ .start
    · exact .start
  | step ch _ hs ih =>
    cases Match.step?_moved hs with
    | place _ _ hg => exact ih.step (step?_sound hg)
    | resolve hg => exact ih.step (step?_sound hg)
    | attack _ hg => exact ih.step (step?_sound hg)
    | declare _ => exact ih
    | block _ hg => exact ih.step (step?_sound hg)
    | tap _ => exact ih
    | endTurn => exact Reachable.drawUpTo _ _ ih

/-- **ターンのない対戦のどの盤面でも成り立つ性質は、ターンのある対戦でも成り立つ**
（盤面の制約、★、受け入れた証明のジョブなど） -/
theorem TReachable.of_reachable {r : Rules} {decks : PlayerId → List Card} {first : PlayerId}
    {P : State → Prop} (hP : ∀ g, Reachable r decks g → P g) {m : Match}
    (h : TReachable r decks first m) : P m.g :=
  hP _ h.reachable

/-! ## ターンがあるから言える性質 -/

@[simp] theorem TurnInfo.prune_tp (t : TurnInfo) (g : State) : (t.prune g).tp = t.tp := rfl
@[simp] theorem TurnInfo.prune_summons (t : TurnInfo) (g : State) : (t.prune g).summons = t.summons := rfl
@[simp] theorem TurnInfo.prune_placed (t : TurnInfo) (g : State) : (t.prune g).placed = t.placed := rfl

/-- **1ターンに置いた戦闘できるカードの枚数は、上限を超えない**（上限があるとき） -/
theorem TReachable.summons_le {r : Rules} {decks : PlayerId → List Card} {first : PlayerId} {m : Match}
    (h : TReachable r decks first m) (hl : r.summonsPerTurn ≠ 0) : m.turn.summons ≤ r.summonsPerTurn := by
  induction h with
  | start => simp [Match.start]
  | step ch _ hs ih =>
    cases Match.step?_moved hs with
    | @place _ _ _ _ _ c _ _ hok _ =>
      simp only [TurnInfo.placeOK, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
        beq_iff_eq, decide_eq_true_eq] at hok
      simp only [TurnInfo.prune_summons, TurnInfo.afterPlace]
      split
      · rename_i hf
        rcases hok.1.1 with (h1 | h1) | h1
        · simp [hf] at h1
        · exact absurd h1 hl
        · omega
      · simpa using ih
    | resolve _ => simpa using ih
    | attack _ _ => simpa [TurnInfo.afterAttack] using ih
    | declare _ => simpa [TurnInfo.afterAttack] using ih
    | block _ _ => simpa [TurnInfo.afterBlock] using ih
    | tap _ => simpa [TurnInfo.afterTap] using ih
    | endTurn => simp [TurnInfo.prune, TurnInfo.next]

/-- **種類ごとの上限：1ターンに置いた、その種類のカードの枚数は上限を超えない**（例：土地は1ターンに1枚） -/
theorem TReachable.placed_le {r : Rules} {decks : PlayerId → List Card} {first : PlayerId} {m : Match}
    (h : TReachable r decks first m) {l : PlaceLimit} (hl : l ∈ r.placeLimits) :
    (m.turn.placed.filter l.types.contains).length ≤ l.count := by
  induction h with
  | start => simp [Match.start]
  | step ch _ hs ih =>
    cases Match.step?_moved hs with
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
    | resolve _ => simpa using ih
    | attack _ _ => simpa [TurnInfo.afterAttack] using ih
    | declare _ => simpa [TurnInfo.afterAttack] using ih
    | block _ _ => simpa [TurnInfo.afterBlock] using ih
    | tap _ => simpa [TurnInfo.afterTap] using ih
    | endTurn => simp [TurnInfo.prune, TurnInfo.next]

/-- 記録はどれも、フィールドのカードの一部（同じカードの枚数も含めて） -/
def TurnInfo.Fits (t : TurnInfo) (g : State) : Prop :=
  BagLe t.attacked (g t.tp).field ∧ BagLe t.entered (g t.tp).field ∧ BagLe t.tapped (g t.tp).field ∧
    BagLe t.oppTapped (g (!t.tp)).field ∧ BagLe t.blocked (g (!t.tp)).field

theorem TurnInfo.prune_fits (t : TurnInfo) (g : State) : (t.prune g).Fits g :=
  ⟨prune_bagLe _ _, prune_bagLe _ _, prune_bagLe _ _, prune_bagLe _ _, prune_bagLe _ _⟩

/-- **攻撃・置いた・タップの記録は、いつもフィールドのカードの一部**
（同じカードの枚数も含めて。だから、フィールドのどのカードも1ターンに1回までしか攻撃できず、
タップしているカードは、起きるまでタップできない） -/
theorem TReachable.fits {r : Rules} {decks : PlayerId → List Card} {first : PlayerId} {m : Match}
    (h : TReachable r decks first m) : m.turn.Fits m.g := by
  induction h with
  | start => refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro a <;> simp [Match.start]
  | step ch _ hs _ =>
    cases Match.step?_moved hs <;> exact TurnInfo.prune_fits _ _

/-- **攻撃したカードの記録は、ターンプレイヤーのフィールドのカードの一部**
（同じカードの枚数も含めて。だから、フィールドのどのカードも1ターンに1回までしか攻撃できない） -/
theorem TReachable.attacked_bagLe {r : Rules} {decks : PlayerId → List Card} {first : PlayerId} {m : Match}
    (h : TReachable r decks first m) : BagLe m.turn.attacked (m.g m.turn.tp).field :=
  h.fits.1

end CardGen
