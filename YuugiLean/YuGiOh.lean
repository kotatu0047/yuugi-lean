/-!
# 遊戯王OCG コアルールの Lean 4 による形式化

Lean 4 コアのみ（Mathlib 不要）で動く、遊戯王OCGの基本ルールのモデルです。

## 形式化している範囲
* カード：モンスター（レベル・攻守・属性・種族）／魔法／罠
* ゾーン：デッキ・手札・モンスターゾーン(5)・魔法罠ゾーン(5)・墓地
* フェイズ：ドロー → スタンバイ → メイン1 → バトル → メイン2 → エンド
* 先攻1ターン目はドローなし・バトルフェイズなし
* 通常召喚／セットは1ターンに1度、レベル5-6は1体・7以上は2体のリリース
* 反転召喚・表示形式の変更（召喚したターン不可、1ターン1度）
* 戦闘ダメージ計算（攻撃表示／守備表示／裏側守備の反転、相打ち、攻撃力0同士）
* 魔法・罠の発動（罠はセットした次のターン以降、相手ターンでも発動可）
* 手札上限6枚（エンドフェイズに捨てる）
* 勝敗：LP 0、デッキ切れ（ドローできない）
* チェーン：スペルスピード1〜3、優先権、両者のパスで逆順に解決、カウンター罠による発動の無効化

## 範囲外（簡略化）
誘発効果・タイミングを逃す・コスト等の効果処理、エクストラデッキ（融合/S/X/L/P）、
特殊召喚、モンスター効果、永続/装備/フィールド等の魔法罠の種類。
チェーンを組めるのは魔法・罠の発動のみで、空きチェーンでは非ターンプレイヤーも発動できる
（ターンプレイヤーが優先権を譲ったものとみなす）。
-/

namespace YGO

/-! ## 1. カード -/

inductive Attribute where
  | dark | light | earth | water | fire | wind | divine
  deriving Repr, DecidableEq

/-- 種族 -/
inductive Race where
  | dragon | spellcaster | warrior | beastWarrior | beast | fiend | zombie
  | machine | aqua | pyro | rock | wingedBeast | plant | insect | thunder
  | fish | seaSerpent | reptile | psychic | fairy | dinosaur
  deriving Repr, DecidableEq

structure MonsterCard where
  name      : String
  level     : Nat
  atk       : Nat
  dfs       : Nat     -- 守備力（`def` は予約語のため）
  attr      : Attribute
  race      : Race
  deriving Repr, DecidableEq

/-- 魔法・罠カードの効果（小さな効果言語） -/
inductive Effect where
  | burn (n : Nat)               -- 相手に n ダメージ
  | heal (n : Nat)               -- 自分の LP を n 回復
  | draw (n : Nat)               -- 自分は n 枚ドロー
  | destroyOppMonsters           -- 相手モンスターを全て破壊
  | destroyAllMonsters           -- フィールドのモンスターを全て破壊
  | burnPerOppMonster (n : Nat)  -- 相手モンスター1体につき n ダメージ
  | negate (oppDraw : Nat)       -- 直前のチェーンブロックの発動を無効にし破壊、その後相手は oppDraw 枚ドロー
  deriving Repr, DecidableEq

def Effect.isNegate : Effect → Bool
  | .negate _ => true
  | _ => false

inductive Card where
  | monster (m : MonsterCard)
  | spell (name : String) (e : Effect)
  | trap  (name : String) (e : Effect)
  | counterTrap (name : String) (e : Effect)
  deriving Repr, DecidableEq

/-- スペルスピード（モンスターは発動しないので 0） -/
def Card.spellSpeed : Card → Nat
  | .monster _ => 0
  | .spell .. => 1
  | .trap .. => 2
  | .counterTrap .. => 3

/-! ## 2. フィールドとプレイヤー -/

inductive Position where
  | attack | faceUpDefense | faceDownDefense
  deriving Repr, DecidableEq

structure FieldMonster where
  card         : MonsterCard
  pos          : Position
  summonedTurn : Nat
  attacked     : Bool := false
  posChanged   : Bool := false
  deriving Repr, DecidableEq

/-- 魔法・罠ゾーンにセットされたカード -/
structure SetCard where
  card    : Card
  setTurn : Nat
  deriving Repr, DecidableEq

def initialLP      : Nat := 8000
def monsterZones   : Nat := 5
def spellTrapZones : Nat := 5
def handLimit      : Nat := 6

structure Player where
  lp       : Nat := initialLP
  deck     : List Card
  hand     : List Card := []
  monsters : List FieldMonster := []
  backrow  : List SetCard := []
  grave    : List Card := []
  deriving Repr, DecidableEq

inductive PlayerId where
  | one | two
  deriving Repr, DecidableEq

def PlayerId.other : PlayerId → PlayerId
  | .one => .two
  | .two => .one

@[simp] theorem PlayerId.other_other (p : PlayerId) : p.other.other = p := by
  cases p <;> rfl

@[simp] theorem PlayerId.other_ne (p : PlayerId) : p.other ≠ p := by
  cases p <;> decide

/-- 盤面：ターン・フェイズに依存しない部分 -/
structure Board where
  p1 : Player
  p2 : Player
  normalSummoned : Bool := false
  deriving Repr, DecidableEq

def Board.get (b : Board) : PlayerId → Player
  | .one => b.p1
  | .two => b.p2

def Board.set (b : Board) : PlayerId → Player → Board
  | .one, p => { b with p1 := p }
  | .two, p => { b with p2 := p }

def Board.modify (b : Board) (i : PlayerId) (f : Player → Player) : Board :=
  b.set i (f (b.get i))

/-- チェーンブロック。発動したカードは解決するまでチェーン上（魔法・罠ゾーン）に残る。 -/
structure ChainLink where
  owner : PlayerId
  card  : Card
  eff   : Effect
  speed : Nat
  deriving Repr, DecidableEq

/-- 盤面とチェーンの状態。`passed` は直前の行動がパスだったか。 -/
structure ChainState where
  board    : Board
  chain    : List ChainLink := []   -- 先頭が最後に積まれたブロック
  priority : PlayerId := .one
  passed   : Bool := false

/-! ## 3. ゲーム状態 -/

inductive Phase where
  | draw | standby | main1 | battle | main2 | ending
  deriving Repr, DecidableEq

inductive Outcome where
  | win (p : PlayerId)
  | draw
  deriving Repr, DecidableEq

structure Game where
  board  : Board
  turn   : Nat          -- 1 始まり
  active : PlayerId     -- ターンプレイヤー
  phase  : Phase
  result : Option Outcome := none
  chain    : List ChainLink := []
  priority : PlayerId := .one
  passed   : Bool := false
  deriving Repr

/-- 各行動から読み取り専用で見えるコンテキスト -/
structure Ctx where
  turn   : Nat
  active : PlayerId
  phase  : Phase

def Game.ctx (g : Game) : Ctx := ⟨g.turn, g.active, g.phase⟩

def Game.cs (g : Game) : ChainState := ⟨g.board, g.chain, g.priority, g.passed⟩

def Game.setCs (g : Game) (s : ChainState) : Game :=
  { g with board := s.board, chain := s.chain, priority := s.priority, passed := s.passed }

/-! ## 4. 基本ルール -/

/-- アドバンス召喚に必要なリリース数 -/
def tributesRequired (level : Nat) : Nat :=
  if level ≤ 4 then 0 else if level ≤ 6 then 1 else 2

def Phase.isMain : Phase → Bool
  | .main1 | .main2 => true
  | _ => false

/-- 戦闘結果 -/
structure BattleResult where
  attackerDestroyed : Bool
  defenderDestroyed : Bool
  dmgToAttacker     : Nat   -- 攻撃側プレイヤーが受ける戦闘ダメージ
  dmgToDefender     : Nat   -- 守備側プレイヤーが受ける戦闘ダメージ
  deriving Repr, DecidableEq

/-- ダメージ計算。`atk` は攻撃モンスターの攻撃力、`pos/tAtk/tDef` は攻撃対象。 -/
def resolveBattle (atk : Nat) (pos : Position) (tAtk tDef : Nat) : BattleResult :=
  match pos with
  | .attack =>
    if tAtk < atk then ⟨false, true, 0, atk - tAtk⟩
    else if atk < tAtk then ⟨true, false, tAtk - atk, 0⟩
    else if atk = 0 then ⟨false, false, 0, 0⟩      -- 攻撃力0同士は何も起きない
    else ⟨true, true, 0, 0⟩                        -- 相打ち
  | _ =>
    if tDef < atk then ⟨false, true, 0, 0⟩          -- 貫通なし
    else if atk < tDef then ⟨false, false, tDef - atk, 0⟩  -- 反射ダメージ
    else ⟨false, false, 0, 0⟩

/-! ## 5. 補助関数 -/

/-- 添字集合 `is` の要素を取り除く。(残り, 取り除いたもの) を返す。 -/
def removeIdxs {α : Type} (l : List α) (is : List Nat) : List α × List α :=
  go 0 l
where
  go : Nat → List α → List α × List α
    | _, [] => ([], [])
    | i, x :: xs =>
      let r := go (i + 1) xs
      if is.contains i then (r.1, x :: r.2) else (x :: r.1, r.2)

theorem removeIdxs_go_length {α : Type} (is : List Nat) :
    ∀ (i : Nat) (l : List α),
      (removeIdxs.go is i l).1.length + (removeIdxs.go is i l).2.length = l.length := by
  intro i l
  induction l generalizing i with
  | nil => rfl
  | cons x xs ih =>
    have := ih (i + 1)
    simp only [removeIdxs.go]
    split <;> simp <;> omega

/-- リリースしてもカードは消えない（残り＋リリース分 = 元の数） -/
theorem removeIdxs_length {α : Type} (l : List α) (is : List Nat) :
    (removeIdxs l is).1.length + (removeIdxs l is).2.length = l.length :=
  removeIdxs_go_length is 0 l

namespace Player

def damage (p : Player) (n : Nat) : Player := { p with lp := p.lp - n }

def heal (p : Player) (n : Nat) : Player := { p with lp := p.lp + n }

def drawOne (p : Player) : Option Player :=
  match p.deck with
  | [] => none
  | c :: cs => some { p with deck := cs, hand := p.hand ++ [c] }

def drawN : Nat → Player → Option Player
  | 0, p => some p
  | n + 1, p => p.drawOne.bind (drawN n)

/-- `i` 番目のモンスターを破壊して墓地へ -/
def destroyAt (p : Player) (i : Nat) : Player :=
  { p with monsters := p.monsters.eraseIdx i
           grave := p.grave ++ (p.monsters[i]?.map (fun m => Card.monster m.card)).toList }

def destroyAll (p : Player) : Player :=
  { p with monsters := []
           grave := p.grave ++ p.monsters.map (fun m => Card.monster m.card) }

/-- ターン開始時のリセット -/
def resetMonsters (p : Player) : Player :=
  { p with monsters := p.monsters.map (fun m => { m with attacked := false, posChanged := false }) }

end Player

/-! ## 6. 行動 -/

inductive Action where
  | nextPhase
  | normalSummon   (hand : Nat) (tributes : List Nat)
  | normalSet      (hand : Nat) (tributes : List Nat)
  | flipSummon     (zone : Nat)
  | changePosition (zone : Nat)
  | activateSpell  (hand : Nat)                  -- 手札から魔法を発動
  | setSpellTrap   (hand : Nat)
  | activateSet    (who : PlayerId) (zone : Nat) -- セットした魔法・罠を発動（罠は相手ターンも可）
  | pass                                         -- 優先権を持つプレイヤーがチェーンせずに譲る
  | attack         (attacker : Nat) (target : Option Nat)
  | discard        (hand : Nat)                  -- エンドフェイズの手札調整
  deriving Repr, DecidableEq

def Action.isNextPhase : Action → Bool
  | .nextPhase => true
  | _ => false

open Except in
/-- 効果の適用。`self` は発動したプレイヤー。 -/
def applyEffect (self : PlayerId) (b : Board) : Effect → Except String Board
  | .burn n => pure (b.modify self.other (·.damage n))
  | .heal n => pure (b.modify self (·.heal n))
  | .draw n =>
    match (b.get self).drawN n with
    | none   => throw "デッキの枚数が足りないため発動できない"
    | some p => pure (b.set self p)
  | .destroyOppMonsters => pure (b.modify self.other Player.destroyAll)
  | .destroyAllMonsters => pure ((b.modify self Player.destroyAll).modify self.other Player.destroyAll)
  | .burnPerOppMonster n =>
    let k := (b.get self.other).monsters.length
    pure (b.modify self.other (·.damage (n * k)))
  | .negate n =>
    -- 無効化そのものは `resolveChain` が行う。ここでは相手のドロー（できる分だけ）
    match (b.get self.other).drawN n with
    | none   => pure b
    | some p => pure (b.set self.other p)

/-! ### チェーン -/

/-- 発動時に確認する条件 -/
def canActivate (self : PlayerId) (b : Board) (chain : List ChainLink) : Effect → Except String Unit
  | .draw n =>
    if n ≤ (b.get self).deck.length then pure () else throw "デッキの枚数が足りないため発動できない"
  | .negate _ => if chain.isEmpty then throw "無効にする発動がない" else pure ()
  | _ => pure ()

def toGrave (b : Board) (l : ChainLink) : Board :=
  b.modify l.owner (fun p => { p with grave := p.grave ++ [l.card] })

/-- 1つのチェーンブロックを解決する。解決時に処理できない効果は不発。 -/
def resolveLink (b : Board) (l : ChainLink) : Board :=
  let b := match applyEffect l.owner b l.eff with
    | .ok b'   => b'
    | .error _ => b
  toGrave b l

/-- チェーンを上（最後に積まれたブロック）から順に解決する。
`neg` はこのブロックの発動が無効にされたかどうか。 -/
def resolveChain : Board → Bool → List ChainLink → Board
  | b, _, [] => b
  | b, neg, l :: rest =>
    resolveChain (if neg then toGrave b l else resolveLink b l) (!neg && l.eff.isNegate) rest

/-- チェーンにブロックを積む。チェーン中は優先権とスペルスピードを確認する。 -/
def pushLink (s : ChainState) (b : Board) (l : ChainLink) : Except String ChainState := do
  match s.chain with
  | [] => pure ()
  | top :: _ =>
    unless l.owner = s.priority do throw "優先権を持っていない"
    unless 2 ≤ l.speed do throw "スペルスピード1はチェーンに組めない"
    unless top.speed ≤ l.speed do
      throw s!"スペルスピード{top.speed}にはスペルスピード{top.speed}以上でしかチェーンできない"
  canActivate l.owner b s.chain l.eff
  return { board := b, chain := l :: s.chain, priority := l.owner.other, passed := false }

/-- パス。両者が続けてパスしたらチェーンを解決する。 -/
def passAct (s : ChainState) : Except String ChainState :=
  if s.chain.isEmpty then throw "チェーンが組まれていない"
  else if s.passed then pure { board := resolveChain s.board false s.chain, priority := s.priority }
  else pure { s with priority := s.priority.other, passed := true }

/-- 通常召喚・セットの共通処理 -/
def summonCore (c : Ctx) (b : Board) (h : Nat) (ts : List Nat) (pos : Position) :
    Except String Board := do
  unless c.phase.isMain do throw "通常召喚はメインフェイズにしか行えない"
  if b.normalSummoned then throw "通常召喚（セット）は1ターンに1度まで"
  let me := b.get c.active
  let some card := me.hand[h]? | throw "手札にそのカードがない"
  let .monster m := card | throw "モンスターカードではない"
  unless ts.eraseDups.length = ts.length do throw "同じモンスターを2回リリースできない"
  unless ts.all (· < me.monsters.length) do throw "リリース対象が存在しない"
  unless ts.length = tributesRequired m.level do
    throw s!"レベル{m.level}の召喚にはリリースが{tributesRequired m.level}体必要"
  let (rest, tributed) := removeIdxs me.monsters ts
  unless rest.length < monsterZones do throw "モンスターゾーンに空きがない"
  let me' := { me with
    hand := me.hand.eraseIdx h
    monsters := rest ++ [{ card := m, pos := pos, summonedTurn := c.turn }]
    grave := me.grave ++ tributed.map (fun t => Card.monster t.card) }
  return { b.set c.active me' with normalSummoned := true }

def attackAct (c : Ctx) (b : Board) (ai : Nat) (tgt : Option Nat) : Except String Board := do
  unless c.phase = .battle do throw "攻撃はバトルフェイズにしか行えない"
  let me := b.get c.active
  let opp := b.get c.active.other
  let some a := me.monsters[ai]? | throw "攻撃モンスターが存在しない"
  unless a.pos = .attack do throw "攻撃表示のモンスターしか攻撃できない"
  if a.attacked then throw "このモンスターはこのターン既に攻撃している"
  let me := { me with monsters := me.monsters.set ai { a with attacked := true } }
  match tgt with
  | none =>
    unless opp.monsters.isEmpty do throw "相手フィールドにモンスターがいるため直接攻撃できない"
    return (b.set c.active me).set c.active.other (opp.damage a.card.atk)
  | some ti =>
    let some d := opp.monsters[ti]? | throw "攻撃対象が存在しない"
    let r := resolveBattle a.card.atk d.pos d.card.atk d.card.dfs
    -- 裏側守備表示は表側にしてからダメージ計算
    let d := if d.pos = .faceDownDefense then { d with pos := .faceUpDefense } else d
    let opp := { opp with monsters := opp.monsters.set ti d }
    let me  := if r.attackerDestroyed then me.destroyAt ai else me
    let opp := if r.defenderDestroyed then opp.destroyAt ti else opp
    return (b.set c.active (me.damage r.dmgToAttacker)).set c.active.other
      (opp.damage r.dmgToDefender)

def changePositionAct (c : Ctx) (b : Board) (i : Nat) : Except String Board := do
  unless c.phase.isMain do throw "表示形式の変更はメインフェイズのみ"
  let me := b.get c.active
  let some m := me.monsters[i]? | throw "モンスターが存在しない"
  if m.summonedTurn = c.turn then throw "召喚・セットしたターンは表示形式を変更できない"
  if m.posChanged || m.attacked then throw "このターン既に表示形式を変更したか攻撃している"
  let newPos ← match m.pos with
    | .attack => pure Position.faceUpDefense
    | .faceUpDefense => pure Position.attack
    | .faceDownDefense => throw "裏側守備表示は反転召喚で表にする"
  return b.set c.active { me with monsters := me.monsters.set i { m with pos := newPos, posChanged := true } }

def flipSummonAct (c : Ctx) (b : Board) (i : Nat) : Except String Board := do
  unless c.phase.isMain do throw "反転召喚はメインフェイズのみ"
  let me := b.get c.active
  let some m := me.monsters[i]? | throw "モンスターが存在しない"
  unless m.pos = .faceDownDefense do throw "裏側守備表示のモンスターではない"
  if m.summonedTurn = c.turn then throw "セットしたターンは反転召喚できない"
  if m.posChanged then throw "このターン既に表示形式を変更している"
  return b.set c.active { me with monsters := me.monsters.set i { m with pos := .attack, posChanged := true } }

def activateSpellAct (c : Ctx) (s : ChainState) (h : Nat) : Except String ChainState := do
  unless c.phase.isMain do throw "魔法カードはメインフェイズに発動する"
  let me := s.board.get c.active
  let some card := me.hand[h]? | throw "手札にそのカードがない"
  let .spell _ e := card | throw "魔法カードではない"
  -- チェーン上の自分のカードも魔法・罠ゾーンを使っている
  unless me.backrow.length + (s.chain.filter (·.owner = c.active)).length < spellTrapZones do
    throw "魔法・罠ゾーンに空きがない"
  pushLink s (s.board.set c.active { me with hand := me.hand.eraseIdx h }) ⟨c.active, card, e, 1⟩

def setSpellTrapAct (c : Ctx) (b : Board) (h : Nat) : Except String Board := do
  unless c.phase.isMain do throw "セットはメインフェイズのみ"
  let me := b.get c.active
  let some card := me.hand[h]? | throw "手札にそのカードがない"
  if let .monster _ := card then throw "モンスターは魔法・罠ゾーンにセットできない"
  unless me.backrow.length < spellTrapZones do throw "魔法・罠ゾーンに空きがない"
  return b.set c.active { me with hand := me.hand.eraseIdx h
                                  backrow := me.backrow ++ [⟨card, c.turn⟩] }

def activateSetAct (c : Ctx) (s : ChainState) (who : PlayerId) (z : Nat) :
    Except String ChainState := do
  let me := s.board.get who
  let some sc := me.backrow[z]? | throw "そのゾーンにカードがない"
  let e ← match sc.card with
    | .trap _ e | .counterTrap _ e =>
      if sc.setTurn < c.turn then pure e else throw "罠はセットしたターンには発動できない"
    | .spell _ e =>
      if who = c.active ∧ c.phase.isMain then pure e
      else throw "通常魔法は自分のメインフェイズにしか発動できない"
    | .monster _ => throw "モンスターは発動できない"
  pushLink s (s.board.set who { me with backrow := me.backrow.eraseIdx z })
    ⟨who, sc.card, e, sc.card.spellSpeed⟩

def discardAct (c : Ctx) (b : Board) (h : Nat) : Except String Board := do
  unless c.phase = .ending do throw "手札を捨てるのはエンドフェイズのみ"
  let me := b.get c.active
  unless me.hand.length > handLimit do throw "手札が上限を超えていない"
  let some card := me.hand[h]? | throw "手札にそのカードがない"
  return b.set c.active { me with hand := me.hand.eraseIdx h, grave := me.grave ++ [card] }

/-- チェーンに関わらない行動。盤面だけを変化させる。 -/
def boardAct (c : Ctx) (b : Board) : Action → Except String Board
  | .normalSummon h ts   => summonCore c b h ts .attack
  | .normalSet h ts      => summonCore c b h ts .faceDownDefense
  | .flipSummon i        => flipSummonAct c b i
  | .changePosition i    => changePositionAct c b i
  | .setSpellTrap h      => setSpellTrapAct c b h
  | .attack a t          => attackAct c b a t
  | .discard h           => discardAct c b h
  | _                    => throw "unreachable"

/-- フェイズ移行以外の行動。チェーンの処理中は発動とパスしか行えない。 -/
def act (c : Ctx) (s : ChainState) : Action → Except String ChainState
  | .pass              => passAct s
  | .activateSpell h   => activateSpellAct c s h
  | .activateSet who z => activateSetAct c s who z
  | a =>
    if s.chain.isEmpty then (boardAct c s.board a).map ({ s with board := · })
    else throw "チェーンの処理中は発動とパスしか行えない"

/-! ## 7. フェイズ進行と勝敗 -/

/-- LP による勝敗判定 -/
def checkResult (g : Game) : Game :=
  { g with result :=
      match g.result with
      | some r => some r
      | none =>
        if g.board.p1.lp = 0 ∧ g.board.p2.lp = 0 then some .draw
        else if g.board.p1.lp = 0 then some (.win .two)
        else if g.board.p2.lp = 0 then some (.win .one)
        else none }

def nextPhase (g : Game) : Except String Game :=
  match g.phase with
  | .draw    => pure { g with phase := .standby }
  | .standby => pure { g with phase := .main1 }
  | .main1   =>
    -- 先攻1ターン目はバトルフェイズを行えない
    if g.turn = 1 then pure { g with phase := .ending } else pure { g with phase := .battle }
  | .battle  => pure { g with phase := .main2 }
  | .main2   => pure { g with phase := .ending }
  | .ending  =>
    if (g.board.get g.active).hand.length > handLimit then
      throw "手札が7枚以上あるので、6枚になるまで捨てなければならない"
    else
      let nxt := g.active.other
      let b := ({ g.board with normalSummoned := false }.modify g.active Player.resetMonsters).modify
        nxt Player.resetMonsters
      let g' := { g with turn := g.turn + 1, active := nxt, phase := .draw }
      match (b.get nxt).drawOne with
      | none   => pure { g' with board := b, result := some (.win g.active) }  -- デッキ切れ
      | some p => pure { g' with board := b.set nxt p }

def step (g : Game) (a : Action) : Except String Game :=
  if g.result.isSome then throw "既に決着がついている"
  else if a.isNextPhase then
    if g.chain.isEmpty then nextPhase g else throw "チェーンの処理中はフェイズを進められない"
  else (act g.ctx g.cs a).map (fun s => checkResult (g.setCs s))

def play (g : Game) (as : List Action) : Except String Game :=
  as.foldlM step g

/-- 初期状態：互いに5枚ドローし、先攻1ターン目のドローフェイズから（先攻はドローしない） -/
def Game.init (d1 d2 : List Card) : Game where
  board := { p1 := { deck := d1.drop 5, hand := d1.take 5 },
             p2 := { deck := d2.drop 5, hand := d2.take 5 } }
  turn := 1
  active := .one
  phase := .draw

/-- 合法な手順で到達可能な状態 -/
inductive Reachable : Game → Prop
  | init (d1 d2 : List Card) : Reachable (Game.init d1 d2)
  | step {g g' : Game} (a : Action) : Reachable g → step g a = .ok g' → Reachable g'

/-! ## 8. 定理 -/

section Theorems

theorem tributes_low (l : Nat) (h : l ≤ 4) : tributesRequired l = 0 := by
  simp [tributesRequired, h]

theorem tributes_mid (l : Nat) (h1 : 5 ≤ l) (h2 : l ≤ 6) : tributesRequired l = 1 := by
  simp [tributesRequired, show ¬l ≤ 4 by omega, h2]

theorem tributes_high (l : Nat) (h : 7 ≤ l) : tributesRequired l = 2 := by
  simp [tributesRequired, show ¬l ≤ 4 by omega, show ¬l ≤ 6 by omega]

/-- リリースは最大2体 -/
theorem tributes_le_two (l : Nat) : tributesRequired l ≤ 2 := by
  unfold tributesRequired
  split
  · omega
  · split <;> omega

/-- 1回の戦闘で両プレイヤーが同時に戦闘ダメージを受けることはない -/
theorem battle_damage_one_sided (a : Nat) (p : Position) (x y : Nat) :
    (resolveBattle a p x y).dmgToAttacker = 0 ∨ (resolveBattle a p x y).dmgToDefender = 0 := by
  unfold resolveBattle; split <;> (repeat' split) <;> simp

/-- 守備表示モンスターとの戦闘では守備側プレイヤーはダメージを受けない（貫通なし） -/
theorem defense_no_damage (a : Nat) (p : Position) (x y : Nat) (hp : p ≠ .attack) :
    (resolveBattle a p x y).dmgToDefender = 0 := by
  unfold resolveBattle; split
  · contradiction
  · repeat' split
    all_goals rfl

/-- 守備表示モンスターを攻撃しても攻撃モンスターは破壊されない -/
theorem attack_defense_safe (a : Nat) (p : Position) (x y : Nat) (hp : p ≠ .attack) :
    (resolveBattle a p x y).attackerDestroyed = false := by
  unfold resolveBattle; split
  · contradiction
  · repeat' split
    all_goals rfl

/-- 攻撃表示同士：攻撃力が上回れば相手を破壊し、差分の戦闘ダメージを与える -/
theorem attack_wins (a x y : Nat) (h : x < a) :
    resolveBattle a .attack x y = ⟨false, true, 0, a - x⟩ := by
  simp [resolveBattle, h]

/-- 攻撃表示同士で攻撃力が等しければ（0でない限り）相打ち -/
theorem attack_tie (a y : Nat) (h : a ≠ 0) :
    resolveBattle a .attack a y = ⟨true, true, 0, 0⟩ := by
  simp [resolveBattle, h]

/-- 戦闘ダメージはステータスの差を超えない -/
theorem battle_damage_bound (a : Nat) (p : Position) (x y : Nat) :
    (resolveBattle a p x y).dmgToAttacker + (resolveBattle a p x y).dmgToDefender
      ≤ max (a - x) (x - a) + max (a - y) (y - a) := by
  unfold resolveBattle; split <;> (repeat' split) <;> simp <;> omega

/-- 決着後はいかなる行動もできない -/
theorem no_action_after_result (g : Game) (a : Action) (h : g.result.isSome) :
    step g a = .error "既に決着がついている" := by
  simp [step, h]; rfl

/-- フェイズ移行以外の行動はターン・フェイズ・ターンプレイヤーを変えない -/
theorem step_preserves_turn (g g' : Game) (a : Action) (ha : a.isNextPhase = false)
    (h : step g a = .ok g') :
    g'.turn = g.turn ∧ g'.phase = g.phase ∧ g'.active = g.active := by
  unfold step at h
  split at h
  · contradiction
  · simp only [ha] at h
    cases hb : act g.ctx g.cs a with
    | error e => simp [hb, Except.map] at h
    | ok s =>
      simp [hb, Except.map] at h
      subst h
      simp [checkResult, Game.setCs]

/-- **通常召喚は1ターンに1度**：召喚済みなら次の通常召喚・セットは必ず失敗する -/
theorem normalSummon_once (c : Ctx) (b b' : Board) (h : Nat) (ts : List Nat) (pos : Position)
    (hs : b.normalSummoned = true) : summonCore c b h ts pos ≠ .ok b' := by
  intro hok
  unfold summonCore at hok
  cases hm : c.phase.isMain <;>
    simp [hm, hs, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hok


/-- 不変条件：ターン数は1以上、かつ1ターン目はバトルフェイズでない -/
def Inv (g : Game) : Prop := 1 ≤ g.turn ∧ (g.turn = 1 → g.phase ≠ .battle)

theorem nextPhase_inv (g g' : Game) (hi : Inv g) (h : nextPhase g = .ok g') : Inv g' := by
  obtain ⟨h1, h2⟩ := hi
  unfold nextPhase at h
  split at h <;> rename_i hp
  · injection h with h; subst h; exact ⟨h1, by simp⟩
  · injection h with h; subst h; exact ⟨h1, by simp⟩
  · split at h <;> injection h with h <;> subst h
    · exact ⟨h1, by simp⟩
    · exact ⟨h1, by simp_all⟩
  · injection h with h; subst h; exact ⟨h1, by simp⟩
  · injection h with h; subst h; exact ⟨h1, by simp⟩
  · split at h
    · cases h
    · dsimp only at h
      split at h <;> injection h with h <;> subst h <;> exact ⟨by simp, by simp⟩

/-- 到達可能な全状態で不変条件が成り立つ -/
theorem reachable_inv (g : Game) (hr : Reachable g) : Inv g := by
  induction hr with
  | init d1 d2 => simp [Inv, Game.init]
  | @step g g' a _ hs ih =>
    cases ha : a.isNextPhase with
    | false =>
      obtain ⟨ht, hp, -⟩ := step_preserves_turn g g' a ha hs
      exact ⟨ht ▸ ih.1, fun h => hp ▸ ih.2 (ht ▸ h)⟩
    | true =>
      unfold step at hs
      split at hs
      · cases hs
      · split at hs
        · exact nextPhase_inv g g' ih hs
        · cases hs

/-- **先攻1ターン目はバトルフェイズに入れない** -/
theorem no_battle_first_turn (g : Game) (hr : Reachable g) (ht : g.turn = 1) :
    g.phase ≠ .battle :=
  (reachable_inv g hr).2 ht

/-- 攻撃はバトルフェイズでのみ成功する -/
theorem attack_requires_battle (c : Ctx) (b b' : Board) (i : Nat) (t : Option Nat)
    (h : attackAct c b i t = .ok b') : c.phase = .battle := by
  unfold attackAct at h
  by_cases hp : c.phase = .battle
  · exact hp
  simp [hp, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h

/-- **先攻1ターン目は攻撃できない**（どの手順で到達しても） -/
theorem no_attack_first_turn (g g' : Game) (hr : Reachable g) (ht : g.turn = 1)
    (i : Nat) (t : Option Nat) : step g (.attack i t) ≠ .ok g' := by
  intro h
  unfold step at h
  split at h
  · cases h
  · simp only [Action.isNextPhase] at h
    cases hb : attackAct g.ctx g.board i t with
    | error e =>
      by_cases hc : g.chain = [] <;>
        simp_all [act, boardAct, Game.cs, Except.map, throw, throwThe, MonadExceptOf.throw]
    | ok b =>
      exact no_battle_first_turn g hr ht (attack_requires_battle g.ctx g.board b i t hb)

/-! ### チェーンの定理 -/

/-- チェーンに積めるのは優先権を持つプレイヤーで、スペルスピード2以上かつ直前のブロック以上 -/
theorem pushLink_chain (s s' : ChainState) (b : Board) (l top : ChainLink) (rest : List ChainLink)
    (hc : s.chain = top :: rest) (h : pushLink s b l = .ok s') :
    l.owner = s.priority ∧ 2 ≤ l.speed ∧ top.speed ≤ l.speed := by
  unfold pushLink at h
  rw [hc] at h
  by_cases h1 : l.owner = s.priority <;> by_cases h2 : 2 ≤ l.speed <;>
    by_cases h3 : top.speed ≤ l.speed <;>
    simp_all [bind, Except.bind, throw, throwThe, MonadExceptOf.throw, pure, Except.pure]

/-- **カウンター罠にはカウンター罠でしかチェーンできない** -/
theorem counter_only_by_counter (s s' : ChainState) (b : Board) (l top : ChainLink)
    (rest : List ChainLink) (hc : s.chain = top :: rest) (ht : top.speed = 3)
    (h : pushLink s b l = .ok s') : 3 ≤ l.speed := by
  have := (pushLink_chain s s' b l top rest hc h).2.2
  omega

/-- **チェーンは逆順に解決される**：無効化を含まないチェーンは、
最後に積まれたブロック（リストの先頭）から1つずつ解決される -/
theorem resolveChain_lifo (b : Board) (ls : List ChainLink)
    (hn : ∀ l ∈ ls, l.eff.isNegate = false) :
    resolveChain b false ls = ls.foldl resolveLink b := by
  induction ls generalizing b with
  | nil => rfl
  | cons l rest ih =>
    simp only [resolveChain, List.foldl, hn l (by simp), Bool.not_false, Bool.true_and,
      Bool.false_eq_true, ite_false]
    exact ih _ (fun x hx => hn x (by simp [hx]))

/-- **無効にされたブロックは効果を適用せずに墓地へ送られる** -/
theorem negated_link_skipped (b : Board) (n l : ChainLink) (rest : List ChainLink)
    (hn : n.eff.isNegate = true) :
    resolveChain b false (n :: l :: rest) =
      resolveChain (toGrave (resolveLink b n) l) false rest := by
  simp [resolveChain, hn]

end Theorems

/-! ## 9. カード例 -/

namespace Cards

def blueEyes       : MonsterCard := ⟨"青眼の白龍",       8, 3000, 2500, .light, .dragon⟩
def darkMagician   : MonsterCard := ⟨"ブラック・マジシャン", 7, 2500, 2100, .dark, .spellcaster⟩
def summonedSkull  : MonsterCard := ⟨"デーモンの召喚",     6, 2500, 1200, .dark, .fiend⟩
def celticGuardian : MonsterCard := ⟨"エルフの剣士",       4, 1400, 1200, .earth, .warrior⟩
def giantSoldier   : MonsterCard := ⟨"岩石の巨兵",         3, 1300, 2000, .earth, .rock⟩
def mysticalElf    : MonsterCard := ⟨"ホーリー・エルフ",   4, 800, 2000, .light, .spellcaster⟩
def kuriboh        : MonsterCard := ⟨"クリボー",           1, 300, 200, .dark, .fiend⟩

def potOfGreed  : Card := .spell "強欲な壺" (.draw 2)
def raigeki     : Card := .spell "サンダー・ボルト" .destroyOppMonsters
def darkHole    : Card := .spell "ブラック・ホール" .destroyAllMonsters
def hinotama    : Card := .spell "火の粉" (.burn 500)
def ookazi      : Card := .spell "昼夜の大火事" (.burn 800)
def dianKeto    : Card := .spell "治療の神 ディアン・ケト" (.heal 1000)
def justDesserts : Card := .trap "仕込みマシンガン" (.burnPerOppMonster 500)
def darkBribe   : Card := .counterTrap "魔宮の賄賂" (.negate 1)

end Cards

/-! ## 10. 対戦例 -/

namespace Demo
open Cards

def deck1 : List Card :=
  [.monster celticGuardian, .monster giantSoldier, potOfGreed, raigeki, hinotama,
   .monster summonedSkull, .monster darkMagician, .monster blueEyes, ookazi]

def deck2 : List Card :=
  [.monster mysticalElf, .monster kuriboh, justDesserts, dianKeto, .monster giantSoldier,
   darkHole, .monster kuriboh]

def np : Action := .nextPhase

/-- 発動して両者がパスし、チェーンを解決する -/
def resolve (a : Action) : List Action := [a, .pass, .pass]

def script : List Action :=
  -- ターン1（先攻・P1）：ドローなし、エルフの剣士を召喚。バトルフェイズは飛ばされる
  [np, np, .normalSummon 0 [], np, np] ++
  -- ターン2（P2）：ホーリー・エルフを裏守備、仕込みマシンガンをセット
  [np, np, .normalSet 0 [], .setSpellTrap 1, np, np, np, np] ++
  -- ターン3（P1）：強欲な壺 → サンダー・ボルト → エルフの剣士をリリースしてデーモンの召喚
  [np, np] ++ resolve (.activateSpell 1) ++ resolve (.activateSpell 1) ++ [.normalSummon 2 [0]] ++
  resolve (.activateSet .two 0) ++     -- P2 が相手ターンに仕込みマシンガン（500×1）
  [np, .attack 0 none,                 -- デーモンの召喚で直接攻撃 2500
   np] ++ resolve (.activateSpell 1) ++ [np, np] ++   -- 火の粉 500
  -- ターン4（P2）：ブラック・ホール → 岩石の巨兵で直接攻撃 → ディアン・ケト
  [np, np] ++ resolve (.activateSpell 3) ++ [.normalSummon 2 [], np, .attack 0 none, np] ++
  resolve (.activateSpell 1) ++ [np, np] ++
  -- ターン5（P1）：昼夜の大火事、岩石の巨兵同士で相打ち
  [np, np] ++ resolve (.activateSpell 3) ++
  [.normalSummon 0 [], np, .attack 0 (some 0), np, np, np]
  -- ターン6 のドローで P2 はデッキ切れ → P1 の勝利

def final : Except String Game := play (Game.init deck1 deck2) script

#eval final.map (fun g => (g.turn, g.board.p1.lp, g.board.p2.lp, g.result))

/-- この対戦は P1 のデッキ切れ勝ちで終わる（カーネルで検証） -/
example : (final.toOption.bind (·.result)) = some (.win .one) := by decide

-- 反則の例
#eval (play (Game.init deck1 deck2) [np, np, np, np]).map (fun g => (g.turn, g.active, g.board.p2.hand.length))
#eval (play (Game.init deck1 deck2) [np, np, .normalSummon 0 [], .normalSummon 0 []]).map (·.turn)
#eval (play (Game.init deck1 deck2) [np, np, np, .attack 0 none]).map (·.turn)
#eval (summonCore ⟨3, .one, .main1⟩
        { p1 := { deck := [], hand := [.monster blueEyes] }, p2 := { deck := [] } } 0 [] .attack).map
        (fun _ => ())

/-! ### チェーンの例
P1 のメインフェイズ1。P1 は手札に昼夜の大火事、魔宮の賄賂をセット済み。
P2 は仕込みマシンガンをセット済み。P1 の場にはエルフの剣士が1体。 -/

def chainStart : Game where
  board := { p1 := { deck := [], hand := [ookazi],
                     monsters := [{ card := celticGuardian, pos := .attack, summonedTurn := 1 }],
                     backrow := [⟨darkBribe, 1⟩] },
             p2 := { deck := [.monster kuriboh], backrow := [⟨justDesserts, 2⟩] } }
  turn := 3
  active := .one
  phase := .main1

/-- C1 昼夜の大火事 → C2 仕込みマシンガン → C3 魔宮の賄賂 → 両者パス
解決は逆順：C3 で P2 が1枚ドローし C2 を無効、C2 は不発で墓地へ、C1 で P2 に 800 -/
def chainScript : List Action :=
  [.activateSpell 0, .activateSet .two 0, .activateSet .one 0, .pass, .pass]

def chainEnd : Except String Game := play chainStart chainScript

#eval chainEnd.map (fun g => (g.board.p1.lp, g.board.p2.lp, g.board.p2.hand.length, g.chain.length))

/-- 仕込みマシンガンは無効にされ、P1 は無傷。P2 は 800 ダメージを受けて1枚ドロー -/
example : chainEnd.toOption.map (fun g => (g.board.p1.lp, g.board.p2.lp, g.board.p2.hand.length))
    = some (8000, 7200, 1) := by decide

-- 反則の例：チェーン中のフェイズ移行、スペルスピード1のチェーン、カウンター罠への通常罠
#eval (play chainStart [.activateSpell 0, .nextPhase]).map (fun _ => ())
#eval (play { chainStart with board := (chainStart.board.modify .one
              (fun p => { p with hand := [ookazi, hinotama] })) }
        [.activateSpell 0, .pass, .activateSpell 0]).map (fun _ => ())
#eval (play { chainStart with board := (chainStart.board.modify .two
              (fun p => { p with backrow := [⟨justDesserts, 2⟩, ⟨justDesserts, 2⟩] })) }
        [.activateSpell 0, .activateSet .two 0, .activateSet .one 0, .activateSet .two 0]).map
        (fun _ => ())

end Demo

end YGO
