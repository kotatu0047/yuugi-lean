/-!
# 遊戯王OCG コアルールの Lean 4 による形式化

Lean 4 コアのみ（Mathlib 不要）で動く、遊戯王OCGの基本ルールのモデルです。

## 形式化している範囲
* カード：モンスター（レベル/ランク/リンク・攻守・属性・種族・チューナー・効果）／魔法／罠
* ゾーン：デッキ・エクストラデッキ・手札・メインモンスターゾーン(5)・エクストラモンスターゾーン・
  魔法罠ゾーン(5)・墓地・X素材
* フェイズ：ドロー → スタンバイ → メイン1 → バトル → メイン2 → エンド
* 先攻1ターン目はドローなし・バトルフェイズなし
* 通常召喚／セットは1ターンに1度、レベル5-6は1体・7以上は2体のリリース
* 反転召喚・表示形式の変更（召喚したターン不可、1ターン1度、リンクモンスターは守備表示にできない）
* 特殊召喚：融合（「融合」の効果）・シンクロ・エクシーズ・リンク召喚、効果による特殊召喚（蘇生・リクルート）
* 戦闘：攻撃宣言 → 両者のパス → ダメージ計算（攻撃表示／守備表示／裏側守備の反転、相打ち、攻撃力0同士）
* 魔法・罠：通常・永続・装備魔法、通常・永続・カウンター罠（罠はセットした次のターン以降）
* モンスター効果：起動効果・誘発即時効果（1ターンに1度）、誘発効果、永続効果、コスト（自身のリリース・X素材）
* チェーン：スペルスピード1〜3、両者のパスで逆順に解決、カウンター罠による発動の無効化
* 優先権：空きチェーンでもターンプレイヤーが優先権を持ち、相手はターンプレイヤーのパスを受けて発動する
* 誘発効果は、チェーンが空になった時点で SEGOC（ターンプレイヤーの効果が先）の順にチェーンを組む
* 効果の無効化（スキルドレイン）：処理時にフィールドに表側表示で存在するモンスターの効果のみ無効
* ライフコスト：自分の LP が 0 以下になるようには払えない
* 手札上限6枚（エンドフェイズに捨てる）
* 勝敗：LP 0、デッキ切れ（ドローできない）

## 範囲外・簡略化
* ペンデュラム、トークン、儀式、フィールド魔法、速攻魔法、コントロール奪取
* リンクマーカー：リンクモンスターはエクストラモンスターゾーンにのみ出せる（各プレイヤー1体まで）
* 誘発効果はすべて強制効果として扱う（任意効果も必ず発動する。そのためタイミングを逃さない）
* デッキからのサーチ・リクルートは、デッキの上から最初に条件を満たすカードを選ぶ
* 攻撃対象がいなくなった場合（巻き戻し）は、その攻撃を終了する
* 効果による特殊召喚・エクストラデッキからの特殊召喚は表側攻撃表示で行う
* フェイズ移行はターンプレイヤーの宣言で行う（相手が発動したい場合は、事前にパスで優先権を受ける）
* ダメージステップ中の発動、「1ターンに1度」の名称指定、蘇生制限
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
  | fish | seaSerpent | reptile | psychic | fairy | dinosaur | cyberse
  deriving Repr, DecidableEq

/-- 誘発効果のきっかけになる出来事 -/
inductive Event where
  | normalSummoned        -- 召喚に成功した
  | specialSummoned       -- 特殊召喚に成功した
  | flipped               -- リバースした
  | destroyedByBattle     -- 戦闘で破壊され墓地へ送られた
  | sentToGraveFromField  -- フィールドから墓地へ送られた
  deriving Repr, DecidableEq

/-- 効果（小さな効果言語）。対象は発動時に選び、解決時に確認する。 -/
inductive Effect where
  | noop                         -- 発動時の効果なし（永続・装備カード）
  | burn (n : Nat)               -- 相手に n ダメージ
  | heal (n : Nat)               -- 自分の LP を n 回復
  | draw (n : Nat)               -- 自分は n 枚ドロー
  | destroyOppMonsters           -- 相手モンスターを全て破壊
  | destroyAllMonsters           -- フィールドのモンスターを全て破壊
  | burnPerOppMonster (n : Nat)  -- 相手モンスター1体につき n ダメージ
  | negate (oppDraw : Nat)       -- 直前の魔法・罠の発動を無効にし破壊、その後相手は oppDraw 枚ドロー
  | destroyTarget                -- 対象のモンスター1体を破壊
  | revive                       -- 対象の墓地のモンスター1体を自分フィールドに特殊召喚
  | fusionSummon                 -- 手札・フィールドの素材を墓地へ送り融合召喚
  | destroyAttacker              -- 攻撃してきた相手モンスターを破壊
  | negateAttack                 -- 相手モンスターの攻撃を無効にする
  | millOpp (n : Nat)            -- 相手のデッキの上から n 枚を墓地へ送る
  | recruit (attr : Attribute) (maxAtk : Nat) -- デッキから攻撃力 maxAtk 以下の attr 属性モンスターを特殊召喚
  | searchMaxDef (maxDef : Nat)  -- デッキから守備力 maxDef 以下のモンスターを手札に加える
  deriving Repr, DecidableEq

def Effect.isNegate : Effect → Bool
  | .negate _ => true
  | _ => false

/-- 永続的に適用される効果 -/
inductive Aura where
  | atkUpOwn (race : Option Race) (n : Nat) -- 自分の（その種族の）表側モンスターの攻撃力 n アップ
  | oppAtkDownPerLevel (n : Nat)            -- 相手の表側モンスターの攻撃力はレベル×n ダウン
  | noAttackLevelGE (n : Nat)               -- レベル n 以上のモンスターは攻撃宣言できない
  | negateMonsterEffects                    -- フィールドの表側表示モンスターの効果を無効にする
  deriving Repr, DecidableEq

/-- モンスター効果のコスト -/
inductive Cost where
  | free
  | tributeSelf           -- このカードをリリース
  | detach (n : Nat)      -- X素材を n 個取り除く
  | payLP (n : Nat)       -- LP を n 払う
  deriving Repr, DecidableEq

inductive MonsterEffect where
  | ignition (cost : Cost) (e : Effect)   -- 起動効果：自分メインフェイズ、スペルスピード1
  | quick (cost : Cost) (e : Effect)      -- 誘発即時効果：スペルスピード2
  | trigger (ev : Event) (e : Effect)     -- 誘発効果：出来事が起きると自動でチェーンに積まれる
  | continuous (a : Aura)                 -- 永続効果：表側表示の間、適用され続ける
  deriving Repr, DecidableEq

def MonsterEffect.aura? : MonsterEffect → Option Aura
  | .continuous a => some a
  | _ => none

inductive MonsterKind where
  | main                              -- メインデッキのモンスター
  | fusion (materials : List String)  -- 融合：指定された名前の素材
  | synchro                           -- シンクロ：チューナー1体 + チューナー以外1体以上
  | xyz (count : Nat)                 -- エクシーズ：ランクと同じレベルのモンスター count 体
  | link (rating : Nat)               -- リンク：モンスター（リンクモンスターはリンクマーカーの数として数えてもよい）
  deriving Repr, DecidableEq

structure MonsterCard where
  name    : String
  level   : Nat     -- エクシーズはランク、リンクは 0
  atk     : Nat
  dfs     : Nat     -- 守備力（`def` は予約語のため）。リンクは 0
  attr    : Attribute
  race    : Race
  kind    : MonsterKind := .main
  tuner   : Bool := false
  effects : List MonsterEffect := []
  deriving Repr, DecidableEq

/-- レベル（エクシーズ・リンクモンスターはレベルを持たない） -/
def MonsterCard.level? (m : MonsterCard) : Option Nat :=
  match m.kind with
  | .xyz _ | .link _ => none
  | _ => some m.level

def MonsterCard.isLink (m : MonsterCard) : Bool :=
  match m.kind with
  | .link _ => true
  | _ => false

inductive SpellKind where
  | normal (e : Effect)
  | continuous (a : Aura)
  | equip (atk : Int)       -- 装備モンスターの攻撃力を atk 変化
  deriving Repr, DecidableEq

inductive TrapKind where
  | normal (e : Effect)
  | continuous (a : Aura) (cost : Cost := .free)
  | counter (e : Effect)
  deriving Repr, DecidableEq

inductive Card where
  | monster (m : MonsterCard)
  | spell (name : String) (k : SpellKind)
  | trap  (name : String) (k : TrapKind)
  deriving Repr, DecidableEq

def Card.name : Card → String
  | .monster m => m.name
  | .spell n _ => n
  | .trap n _ => n

/-- スペルスピード（モンスターは発動しないので 0） -/
def Card.spellSpeed : Card → Nat
  | .monster _ => 0
  | .spell .. => 1
  | .trap _ (.counter _) => 3
  | .trap .. => 2

/-- 魔法・罠を発動したときの効果 -/
def Card.activationEffect : Card → Effect
  | .spell _ (.normal e) => e
  | .trap _ (.normal e) => e
  | .trap _ (.counter e) => e
  | _ => .noop

def Card.aura? : Card → Option Aura
  | .spell _ (.continuous a) => some a
  | .trap _ (.continuous a _) => some a
  | _ => none

/-- 発動時に払う LP -/
def Card.lpCost : Card → Nat
  | .trap _ (.continuous _ (.payLP n)) => n
  | _ => 0

def Card.isEquip : Card → Bool
  | .spell _ (.equip _) => true
  | _ => false

def Card.equipAtk : Card → Int
  | .spell _ (.equip n) => n
  | _ => 0

/-! ## 2. フィールドとプレイヤー -/

inductive Position where
  | attack | faceUpDefense | faceDownDefense
  deriving Repr, DecidableEq

structure FieldMonster where
  uid          : Nat            -- フィールドに出るたびに振られる識別子
  card         : MonsterCard
  pos          : Position
  summonedTurn : Nat
  attacked     : Bool := false
  posChanged   : Bool := false
  effectUsed   : Bool := false  -- 起動効果・誘発即時効果を使った（1ターンに1度）
  overlays     : List Card := [] -- X素材
  emz          : Bool := false  -- エクストラモンスターゾーンにいる
  deriving Repr, DecidableEq

/-- 魔法・罠ゾーンのカード -/
structure SetCard where
  card    : Card
  setTurn : Nat
  faceUp  : Bool := false        -- 表側表示（発動済みの永続・装備カード）
  equipTo : Option Nat := none   -- 装備しているモンスターの uid
  deriving Repr, DecidableEq

def initialLP      : Nat := 8000
def monsterZones   : Nat := 5
def spellTrapZones : Nat := 5
def handLimit      : Nat := 6

structure Player where
  lp       : Nat := initialLP
  deck     : List Card
  extra    : List Card := []
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

/-- 宣言中の攻撃 -/
structure AttackDecl where
  attacker : Nat           -- uid
  target   : Option Nat    -- uid（none は直接攻撃）
  deriving Repr, DecidableEq

/-- 誘発効果のために記録する出来事 -/
structure Happened where
  who  : PlayerId
  card : MonsterCard
  ev   : Event
  uid  : Nat     -- 出来事が起きたときの uid
  deriving Repr, DecidableEq

/-- 盤面：ターン・フェイズに依存しない部分 -/
structure Board where
  p1 : Player
  p2 : Player
  normalSummoned : Bool := false
  nextUid : Nat := 0
  attack  : Option AttackDecl := none
  log     : List Happened := []
  deriving Repr, DecidableEq

def Board.get (b : Board) : PlayerId → Player
  | .one => b.p1
  | .two => b.p2

def Board.set (b : Board) : PlayerId → Player → Board
  | .one, p => { b with p1 := p }
  | .two, p => { b with p2 := p }

def Board.modify (b : Board) (i : PlayerId) (f : Player → Player) : Board :=
  b.set i (f (b.get i))

/-- 選択した対象・素材（行動の引数）。フィールドのモンスターは添字で指定する。 -/
structure Args where
  hand    : List Nat := []                  -- 手札（融合素材）
  mine    : List Nat := []                  -- 自分のモンスター（融合素材）
  targets : List (PlayerId × Nat) := []     -- 対象とするフィールドのモンスター
  grave   : Option (PlayerId × Nat) := none -- 対象とする墓地のカード
  extra   : Option Nat := none              -- エクストラデッキのカード
  deriving Repr, DecidableEq

/-- チェーンブロック。対象は uid や「位置と中身」で記録し、解決時に確認する。 -/
structure ChainLink where
  owner       : PlayerId
  card        : Card
  eff         : Effect
  speed       : Nat
  mon         : Bool := false                    -- モンスター効果か
  src         : Option Nat := none               -- 効果を発動したモンスターの uid
  targets     : List Nat := []                   -- 対象モンスターの uid
  graveTarget : Option (PlayerId × Nat × Card) := none
  handMats    : List (Nat × Card) := []
  fieldMats   : List Nat := []
  extra       : Option (Nat × Card) := none
  deriving Repr, DecidableEq

/-- 盤面・チェーン・優先権。`passed` は直前の行動がパスだったか。 -/
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

/-- シンクロ召喚の条件：チューナー1体とチューナー以外1体以上、レベルの合計が等しい -/
def synchroOk (em : MonsterCard) (ms : List MonsterCard) : Bool :=
  (ms.filter (·.tuner)).length == 1 && 2 ≤ ms.length &&
    ms.all (·.level?.isSome) && (ms.map (·.level?.getD 0)).sum == em.level

/-- エクシーズ召喚の条件：ランクと同じレベルのモンスター n 体 -/
def xyzOk (n rank : Nat) (ms : List MonsterCard) : Bool :=
  ms.length == n && ms.all (·.level? == some rank)

/-- リンク素材として数えられる値の候補（リンクモンスターは 1 またはリンクマーカーの数） -/
def linkSums (ms : List MonsterCard) : List Nat :=
  ms.foldr (fun m acc => acc.flatMap fun s =>
    match m.kind with
    | .link r => [s + 1, s + r]
    | _ => [s + 1]) [0]

/-- リンク召喚の条件 -/
def linkOk (rating : Nat) (ms : List MonsterCard) : Bool :=
  ms.length ≤ rating && (linkSums ms).contains rating

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

/-- 取り除いてもカードは消えない（残り＋取り除いた分 = 元の数） -/
theorem removeIdxs_length {α : Type} (l : List α) (is : List Nat) :
    (removeIdxs l is).1.length + (removeIdxs l is).2.length = l.length :=
  removeIdxs_go_length is 0 l

/-- 発動したカード（手札の `h` 番目）を取り除いた後の手札での位置 -/
def shiftIdx (h i : Nat) : Option Nat :=
  if i < h then some i else if h < i then some (i - 1) else none

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

/-- ターン開始時のリセット -/
def resetMonsters (p : Player) : Player :=
  { p with monsters := p.monsters.map fun m =>
      { m with attacked := false, posChanged := false, effectUsed := false } }

def hasEmz (p : Player) : Bool := p.monsters.any (·.emz)

def mainFree (p : Player) : Bool :=
  (p.monsters.filter (fun m => !m.emz)).length < monsterZones

/-- uid が `removed` のモンスターが離れた後、エクストラデッキのモンスターを出せる場所。
`some false` はメインモンスターゾーン、`some true` はエクストラモンスターゾーン。 -/
def slotAfter (p : Player) (removed : List Nat) (isLink : Bool) : Option Bool :=
  let rest := p.monsters.filter (fun m => !removed.contains m.uid)
  if !isLink && (rest.filter (fun m => !m.emz)).length < monsterZones then some false
  else if !rest.any (·.emz) then some true
  else none

/-- 表側の永続魔法・罠の効果 -/
def stAuras (p : Player) : List Aura :=
  p.backrow.filterMap (fun s => if s.faceUp then s.card.aura? else none)

/-- 表側モンスターの永続効果 -/
def monAuras (p : Player) : List Aura :=
  (p.monsters.filter (·.pos ≠ .faceDownDefense)).flatMap
    (fun m => m.card.effects.filterMap MonsterEffect.aura?)

end Player

namespace Board

def findMon (b : Board) (uid : Nat) : Option (PlayerId × FieldMonster) :=
  match b.p1.monsters.find? (·.uid == uid) with
  | some m => some (.one, m)
  | none => (b.p2.monsters.find? (·.uid == uid)).map (.two, ·)

def updMon (b : Board) (w : PlayerId) (uid : Nat) (f : FieldMonster → FieldMonster) : Board :=
  b.modify w fun p => { p with monsters := p.monsters.map fun m => if m.uid = uid then f m else m }

/-- 適用中の永続効果とそのコントローラー。モンスターの効果が無効化されていればモンスターの永続効果は含めない。 -/
def auras (b : Board) : List (PlayerId × Aura) :=
  let st := b.p1.stAuras.map (PlayerId.one, ·) ++ b.p2.stAuras.map (PlayerId.two, ·)
  if st.any (·.2 == .negateMonsterEffects) then st
  else st ++ b.p1.monAuras.map (PlayerId.one, ·) ++ b.p2.monAuras.map (PlayerId.two, ·)

/-- フィールドの表側表示モンスターの効果が無効化されているか -/
def monsterEffectsNegated (b : Board) : Bool :=
  b.auras.any (·.2 == .negateMonsterEffects)

/-- 永続効果による攻撃力の変化。`own` は永続効果のコントローラーがモンスターと同じか。 -/
def _root_.YGO.Aura.atkMod (a : Aura) (own : Bool) (c : MonsterCard) : Int :=
  match a with
  | .atkUpOwn r n =>
    if own && (match r with | none => true | some r => c.race == r) then n else 0
  | .oppAtkDownPerLevel n => if own then 0 else -((c.level?.getD 0 * n : Nat) : Int)
  | .noAttackLevelGE _ | .negateMonsterEffects => 0

/-- 装備カード・永続効果を適用した攻撃力（0 未満にはならない） -/
def atkOf (b : Board) (w : PlayerId) (m : FieldMonster) : Nat :=
  if m.pos = .faceDownDefense then m.card.atk else
  let equip : Int := (b.p1.backrow ++ b.p2.backrow).foldl
    (fun acc s => if s.faceUp && s.equipTo == some m.uid then acc + s.card.equipAtk else acc) 0
  let aura : Int := b.auras.foldl (fun acc (v, a) => acc + a.atkMod (v == w) m.card) 0
  ((m.card.atk : Int) + equip + aura).toNat

/-- 永続効果により攻撃宣言できないか -/
def cannotAttack (b : Board) (m : MonsterCard) : Bool :=
  b.auras.any fun (_, a) =>
    match a, m.level? with
    | .noAttackLevelGE n, some l => n ≤ l
    | _, _ => false

/-- モンスターをフィールドに出す -/
def place (b : Board) (w : PlayerId) (c : MonsterCard) (pos : Position) (turn : Nat)
    (emz : Bool := false) (ev : Option Event := none) (overlays : List Card := []) : Board :=
  let uid := b.nextUid
  let b := b.modify w fun p =>
    { p with monsters := p.monsters ++ [{ uid, card := c, pos, summonedTurn := turn, emz, overlays }] }
  { b with nextUid := uid + 1, log := b.log ++ (ev.map (Happened.mk w c · uid)).toList }

/-- uid のモンスターをフィールドから取り除く。そのモンスターの装備カードは墓地へ送られる。 -/
def detach (b : Board) (uid : Nat) : Option (Board × PlayerId × FieldMonster) := do
  let (w, m) ← b.findMon uid
  let b := b.modify w fun p => { p with monsters := p.monsters.filter (·.uid != uid) }
  let dropEquips (p : Player) : Player :=
    let (eqs, rest) := p.backrow.partition (·.equipTo == some uid)
    { p with backrow := rest, grave := p.grave ++ eqs.map (·.card) }
  pure ((b.modify .one dropEquips).modify .two dropEquips, w, m)

/-- uid のモンスターを墓地へ送る（X素材も墓地へ）。`battle` は戦闘による破壊か。 -/
def toGraveMon (b : Board) (uid : Nat) (battle : Bool := false) : Board :=
  match b.detach uid with
  | none => b
  | some (b, w, m) =>
    let b := b.modify w fun p => { p with grave := p.grave ++ m.overlays ++ [.monster m.card] }
    let evs := (if battle then [Event.destroyedByBattle] else []) ++ [.sentToGraveFromField]
    { b with log := b.log ++ evs.map (Happened.mk w m.card · uid) }

def destroyAllOf (b : Board) (w : PlayerId) : Board :=
  (b.get w).monsters.foldl (fun b m => b.toGraveMon m.uid) b

end Board

/-! ## 6. 行動 -/

inductive Action where
  | nextPhase
  | normalSummon    (hand : Nat) (tributes : List Nat)
  | normalSet       (hand : Nat) (tributes : List Nat)
  | flipSummon      (zone : Nat)
  | changePosition  (zone : Nat)
  | extraSummon     (extra : Nat) (materials : List Nat)   -- シンクロ・エクシーズ・リンク召喚
  | activateSpell   (hand : Nat) (args : Args := {})       -- 手札から魔法を発動
  | setSpellTrap    (hand : Nat)
  | activateSet     (who : PlayerId) (zone : Nat) (args : Args := {}) -- セットした魔法・罠を発動
  | activateMonster (who : PlayerId) (zone : Nat) (eff : Nat := 0) (args : Args := {})
  | pass                                                    -- 優先権を相手に渡す
  | attack          (attacker : Nat) (target : Option Nat)  -- 攻撃宣言
  | discard         (hand : Nat)                            -- エンドフェイズの手札調整
  deriving Repr, DecidableEq

def Action.isNextPhase : Action → Bool
  | .nextPhase => true
  | _ => false

/-! ### 効果 -/

/-- 対象の墓地のモンスターを蘇生できるか -/
def reviveOk (b : Board) (l : ChainLink) : Option (PlayerId × Nat × MonsterCard) := do
  let (w, i, cd) ← l.graveTarget
  guard ((b.get w).grave[i]? = some cd)
  let .monster m := cd | none
  guard (b.get l.owner).mainFree
  pure (w, i, m)

/-- 融合召喚できるか。できるなら融合モンスターとエクストラデッキでの位置を返す。 -/
def fusionPlan (b : Board) (l : ChainLink) : Option (MonsterCard × Nat × Bool) := do
  let p := b.get l.owner
  let (i, c) ← l.extra
  guard (p.extra[i]? = some c)
  let .monster fm := c | none
  let .fusion req := fm.kind | none
  guard (l.handMats.all fun (j, hc) => p.hand[j]? == some hc)
  guard ((l.handMats.map (·.1)).eraseDups.length = l.handMats.length)
  guard (l.fieldMats.eraseDups.length = l.fieldMats.length)
  let fms ← l.fieldMats.mapM fun u => p.monsters.find? (·.uid == u)
  let names := l.handMats.filterMap (fun (_, hc) =>
      match hc with
      | .monster m => some m.name
      | _ => none) ++ fms.map (·.card.name)
  guard (names.length = req.length)
  guard (l.handMats.length + fms.length = req.length)
  guard (req.all fun n => names.count n == req.count n)
  let emz ← p.slotAfter l.fieldMats false
  pure (fm, i, emz)

/-- 効果の適用。解決時に処理できない部分は何もしない。 -/
def applyEffect (c : Ctx) (l : ChainLink) (b : Board) : Board :=
  let self := l.owner
  match l.eff with
  | .noop => b
  | .burn n => b.modify self.other (·.damage n)
  | .heal n => b.modify self (·.heal n)
  | .draw n =>
    match (b.get self).drawN n with
    | none   => b
    | some p => b.set self p
  | .destroyOppMonsters => b.destroyAllOf self.other
  | .destroyAllMonsters => (b.destroyAllOf self).destroyAllOf self.other
  | .burnPerOppMonster n =>
    b.modify self.other (·.damage (n * (b.get self.other).monsters.length))
  | .negate n =>
    -- 無効化そのものは `resolveChain` が行う。ここでは相手のドロー（できる分だけ）
    match (b.get self.other).drawN n with
    | none   => b
    | some p => b.set self.other p
  | .destroyTarget => l.targets.foldl (fun b u => b.toGraveMon u) b
  | .revive =>
    match reviveOk b l with
    | none => b
    | some (w, i, m) =>
      (b.modify w fun p => { p with grave := p.grave.eraseIdx i }).place self m .attack c.turn
        false (some .specialSummoned)
  | .fusionSummon =>
    match fusionPlan b l with
    | none => b
    | some (fm, i, emz) =>
      let b := b.modify self fun p =>
        { p with hand := (removeIdxs p.hand (l.handMats.map (·.1))).1
                 grave := p.grave ++ l.handMats.map (·.2)
                 extra := p.extra.eraseIdx i }
      let b := l.fieldMats.foldl (fun b u => b.toGraveMon u) b
      b.place self fm .attack c.turn emz (some .specialSummoned)
  | .destroyAttacker =>
    match b.attack with
    | some bt => { b.toGraveMon bt.attacker with attack := none }
    | none => b
  | .negateAttack => { b with attack := none }
  | .millOpp n =>
    b.modify self.other fun p => { p with deck := p.deck.drop n, grave := p.grave ++ p.deck.take n }
  | .recruit attr mx =>
    let p := b.get self
    let ok : Card → Bool
      | .monster m => m.attr == attr && m.atk ≤ mx
      | _ => false
    match p.deck.findIdx? ok, p.deck.find? ok with
    | some i, some (.monster m) =>
      if p.mainFree then
        (b.set self { p with deck := p.deck.eraseIdx i }).place self m .attack c.turn
          false (some .specialSummoned)
      else b
    | _, _ => b
  | .searchMaxDef d =>
    let p := b.get self
    let ok : Card → Bool
      | .monster m => m.dfs ≤ d
      | _ => false
    match p.deck.findIdx? ok, p.deck.find? ok with
    | some i, some cd => b.set self { p with deck := p.deck.eraseIdx i, hand := p.hand ++ [cd] }
    | _, _ => b

/-! ### チェーン -/

/-- 発動時に確認する条件 -/
def canActivate (b : Board) (chain : List ChainLink) (l : ChainLink) : Except String Unit := do
  if l.card.isEquip && !l.mon then
    match l.targets with
    | [u] =>
      match b.findMon u with
      | some (_, m) => if m.pos = .faceDownDefense then throw "裏側表示のモンスターには装備できない"
      | none => throw "装備対象が存在しない"
    | _ => throw "装備魔法はモンスター1体を対象にする"
  match l.eff with
  | .draw n =>
    unless n ≤ (b.get l.owner).deck.length do throw "デッキの枚数が足りないため発動できない"
  | .negate _ =>
    match chain with
    | top :: _ => if top.mon then throw "モンスター効果の発動は無効にできない"
    | [] => throw "無効にする発動がない"
  | .destroyTarget =>
    match l.targets with
    | [u] => unless (b.findMon u).isSome do throw "対象が存在しない"
    | _ => throw "モンスター1体を対象にする"
  | .revive => unless (reviveOk b l).isSome do throw "蘇生できるモンスターがいない、またはゾーンに空きがない"
  | .fusionSummon => unless (fusionPlan b l).isSome do throw "融合召喚の条件を満たしていない"
  | .destroyAttacker | .negateAttack =>
    match b.attack with
    | some bt =>
      unless (b.findMon bt.attacker).map (·.1) == some l.owner.other do
        throw "相手モンスターの攻撃宣言時ではない"
    | none => throw "攻撃宣言時ではない"
  | _ => pure ()

/-- 選択した対象・素材をチェーンブロックに記録する。
`shift` は手札から発動したカードの位置（手札の添字をずらすため）。 -/
def mkLink (b : Board) (who : PlayerId) (card : Card) (eff : Effect) (speed : Nat) (args : Args)
    (shift : Option Nat) : Except String ChainLink := do
  let tg ← args.targets.mapM fun (w, i) =>
    match (b.get w).monsters[i]? with
    | some m => pure m.uid
    | none => throw "対象が存在しない"
  let gt ← match args.grave with
    | none => pure none
    | some (w, i) =>
      match (b.get w).grave[i]? with
      | some cd => pure (some (w, i, cd))
      | none => throw "墓地にそのカードがない"
  let hm ← args.hand.mapM fun i => do
    let j ← match shift with
      | none => pure i
      | some h =>
        match shiftIdx h i with
        | some j => pure j
        | none => throw "発動したカード自身は素材にできない"
    match (b.get who).hand[j]? with
    | some cd => pure (j, cd)
    | none => throw "手札にそのカードがない"
  let fm ← args.mine.mapM fun i =>
    match (b.get who).monsters[i]? with
    | some m => pure m.uid
    | none => throw "素材が存在しない"
  let ex ← match args.extra with
    | none => pure none
    | some i =>
      match (b.get who).extra[i]? with
      | some cd => pure (some (i, cd))
      | none => throw "エクストラデッキにそのカードがない"
  pure { owner := who, card, eff, speed, targets := tg, graveTarget := gt, handMats := hm,
         fieldMats := fm, extra := ex }

/-- 魔法・罠を墓地へ送る（モンスター効果ならそのまま） -/
def toGrave (b : Board) (l : ChainLink) : Board :=
  if l.mon then b else b.modify l.owner (fun p => { p with grave := p.grave ++ [l.card] })

/-- モンスター効果の処理時、そのモンスターがフィールドに表側表示で存在し、効果が無効化されているか。
フィールドを離れたモンスター（コストでリリースした、墓地で発動した等）の効果は無効にならない。 -/
def Board.effectNegated (b : Board) (l : ChainLink) : Bool :=
  l.mon && b.monsterEffectsNegated &&
    match l.src.bind b.findMon with
    | some (_, m) => m.pos != .faceDownDefense
    | none => false

/-- 1つのチェーンブロックを解決する。永続・装備カードはフィールドに表側で残る。 -/
def resolveLink (c : Ctx) (b : Board) (l : ChainLink) : Board :=
  let b := if b.effectNegated l then b else applyEffect c l b
  if l.mon then b else
  let keep (eq : Option Nat) : Board :=
    b.modify l.owner fun p =>
      { p with backrow := p.backrow ++ [{ card := l.card, setTurn := c.turn, faceUp := true, equipTo := eq }] }
  match l.card with
  | .spell _ (.continuous _) | .trap _ (.continuous ..) => keep none
  | .spell _ (.equip _) =>
    match l.targets with
    | [u] =>
      match b.findMon u with
      | some (_, m) => if m.pos = .faceDownDefense then toGrave b l else keep (some u)
      | none => toGrave b l
    | _ => toGrave b l
  | _ => toGrave b l

/-- チェーンを上（最後に積まれたブロック）から順に解決する。
`neg` はこのブロックの発動が無効にされたかどうか。 -/
def resolveChain (c : Ctx) : Board → Bool → List ChainLink → Board
  | b, _, [] => b
  | b, neg, l :: rest =>
    resolveChain c (if neg then toGrave b l else resolveLink c b l) (!neg && l.eff.isNegate) rest

/-- チェーンにブロックを積む。優先権とスペルスピードを確認する。 -/
def pushLink (s : ChainState) (b : Board) (l : ChainLink) : Except String ChainState := do
  unless l.owner = s.priority do throw "優先権を持っていない"
  match s.chain with
  | [] => pure ()
  | top :: _ =>
    unless 2 ≤ l.speed do throw "スペルスピード1はチェーンに組めない"
    unless top.speed ≤ l.speed do
      throw s!"スペルスピード{top.speed}にはスペルスピード{top.speed}以上でしかチェーンできない"
  return { board := b, chain := l :: s.chain, priority := l.owner.other, passed := false }

def activateSpellAct (c : Ctx) (s : ChainState) (h : Nat) (args : Args) :
    Except String ChainState := do
  unless c.phase.isMain do throw "魔法カードはメインフェイズに発動する"
  let me := s.board.get c.active
  let some card := me.hand[h]? | throw "手札にそのカードがない"
  let .spell .. := card | throw "魔法カードではない"
  -- チェーン上の自分の魔法・罠も魔法・罠ゾーンを使っている
  unless me.backrow.length + (s.chain.filter (fun l => l.owner = c.active && !l.mon)).length
      < spellTrapZones do
    throw "魔法・罠ゾーンに空きがない"
  let b := s.board.set c.active { me with hand := me.hand.eraseIdx h }
  let l ← mkLink b c.active card card.activationEffect 1 args (some h)
  canActivate b s.chain l
  pushLink s b l

def activateSetAct (c : Ctx) (s : ChainState) (who : PlayerId) (z : Nat) (args : Args) :
    Except String ChainState := do
  let me := s.board.get who
  let some sc := me.backrow[z]? | throw "そのゾーンにカードがない"
  if sc.faceUp then throw "表側表示のカードは発動できない"
  match sc.card with
  | .trap .. => unless sc.setTurn < c.turn do throw "罠はセットしたターンには発動できない"
  | .spell .. =>
    unless who = c.active ∧ c.phase.isMain do throw "魔法は自分のメインフェイズにしか発動できない"
  | .monster _ => throw "モンスターは発動できない"
  let b := s.board.set who { me with backrow := me.backrow.eraseIdx z }
  let l ← mkLink b who sc.card sc.card.activationEffect sc.card.spellSpeed args none
  canActivate b s.chain l
  -- LP が 0 以下になるようには払えない（コストがなければ 0 < LP は常に成り立つ）
  unless sc.card.lpCost < (b.get who).lp do throw "LP が足りないため発動できない"
  pushLink s (b.modify who (·.damage sc.card.lpCost)) l

def activateMonsterAct (c : Ctx) (s : ChainState) (who : PlayerId) (z i : Nat) (args : Args) :
    Except String ChainState := do
  let b := s.board
  let some m := (b.get who).monsters[z]? | throw "モンスターが存在しない"
  if m.pos = .faceDownDefense then throw "裏側表示のモンスターの効果は発動できない"
  let some me := m.card.effects[i]? | throw "その効果はない"
  let (cost, e, speed) ← match me with
    | .ignition cost e =>
      unless who = c.active ∧ c.phase.isMain do throw "起動効果は自分のメインフェイズにしか発動できない"
      pure (cost, e, 1)
    | .quick cost e => pure (cost, e, 2)
    | _ => throw "誘発効果・永続効果は自分で発動するものではない"
  if m.effectUsed then throw "この効果は1ターンに1度しか使えない"
  let l ← mkLink b who (.monster m.card) e speed args none
  let l := { l with mon := true, src := some m.uid }
  canActivate b s.chain l
  -- コストの支払い
  let b := b.updMon who m.uid fun x => { x with effectUsed := true }
  let b ← match cost with
    | .free => pure b
    | .tributeSelf => pure (b.toGraveMon m.uid)
    | .payLP n =>
      if n < (b.get who).lp then pure (b.modify who (·.damage n)) else throw "LP が足りない"
    | .detach n =>
      if n ≤ m.overlays.length then
        pure ((b.updMon who m.uid fun x => { x with overlays := m.overlays.drop n }).modify who
          fun p => { p with grave := p.grave ++ m.overlays.take n })
      else throw "X素材が足りない"
  pushLink s b l

/-! ### 召喚・戦闘 -/

/-- 通常召喚・セットの共通処理 -/
def summonCore (c : Ctx) (b : Board) (h : Nat) (ts : List Nat) (pos : Position) :
    Except String Board := do
  unless c.phase.isMain do throw "通常召喚はメインフェイズにしか行えない"
  if b.normalSummoned then throw "通常召喚（セット）は1ターンに1度まで"
  let me := b.get c.active
  let some card := me.hand[h]? | throw "手札にそのカードがない"
  let .monster m := card | throw "モンスターカードではない"
  unless m.kind = .main do throw "エクストラデッキのモンスターは通常召喚できない"
  unless ts.eraseDups.length = ts.length do throw "同じモンスターを2回リリースできない"
  let some tms := ts.mapM (me.monsters[·]?) | throw "リリース対象が存在しない"
  unless ts.length = tributesRequired m.level do
    throw s!"レベル{m.level}の召喚にはリリースが{tributesRequired m.level}体必要"
  let rest := me.monsters.filter (fun x => !(tms.map (·.uid)).contains x.uid)
  unless (rest.filter (fun x => !x.emz)).length < monsterZones do throw "モンスターゾーンに空きがない"
  let b := tms.foldl (fun b t => b.toGraveMon t.uid) b
  let b := b.modify c.active fun p => { p with hand := p.hand.eraseIdx h }
  let b := b.place c.active m pos c.turn false (if pos = .attack then some .normalSummoned else none)
  return { b with normalSummoned := true }

/-- シンクロ・エクシーズ・リンク召喚 -/
def extraSummonAct (c : Ctx) (b : Board) (ei : Nat) (mats : List Nat) : Except String Board := do
  unless c.phase.isMain do throw "エクストラデッキからの特殊召喚はメインフェイズに行う"
  let me := b.get c.active
  let some (.monster em) := me.extra[ei]? | throw "エクストラデッキにそのモンスターがない"
  unless mats.eraseDups.length = mats.length do throw "同じモンスターを2回素材にできない"
  let some ms := mats.mapM (me.monsters[·]?) | throw "素材が存在しない"
  unless ms.all (·.pos ≠ .faceDownDefense) do throw "素材は表側表示でなければならない"
  let cards := ms.map (·.card)
  let ok := match em.kind with
    | .synchro => synchroOk em cards
    | .xyz n => xyzOk n em.level cards
    | .link r => linkOk r cards
    | _ => false
  unless ok do throw s!"{em.name}の召喚条件を満たしていない"
  let some emz := me.slotAfter (ms.map (·.uid)) em.isLink | throw "モンスターゾーンに空きがない"
  let b := b.modify c.active fun p => { p with extra := p.extra.eraseIdx ei }
  match em.kind with
  | .xyz _ =>
    -- 素材は墓地へ送らず、X素材として重ねる
    let b := ms.foldl (fun b m => match b.detach m.uid with | some (b, _, _) => b | none => b) b
    let b := b.modify c.active fun p => { p with grave := p.grave ++ ms.flatMap (·.overlays) }
    return b.place c.active em .attack c.turn emz (some .specialSummoned)
      (ms.map fun m => Card.monster m.card)
  | _ =>
    let b := ms.foldl (fun b m => b.toGraveMon m.uid) b
    return b.place c.active em .attack c.turn emz (some .specialSummoned)

/-- 攻撃宣言。ダメージ計算は両者がパスした後に `performBattle` で行う。 -/
def declareAttack (c : Ctx) (b : Board) (ai : Nat) (tgt : Option Nat) : Except String Board := do
  unless c.phase = .battle do throw "攻撃はバトルフェイズにしか行えない"
  let me := b.get c.active
  let opp := b.get c.active.other
  let some a := me.monsters[ai]? | throw "攻撃モンスターが存在しない"
  unless a.pos = .attack do throw "攻撃表示のモンスターしか攻撃できない"
  if a.attacked then throw "このモンスターはこのターン既に攻撃している"
  if b.cannotAttack a.card then throw "永続効果により攻撃宣言できない"
  let tu ← match tgt with
    | none =>
      if opp.monsters.isEmpty then pure none
      else throw "相手フィールドにモンスターがいるため直接攻撃できない"
    | some ti =>
      match opp.monsters[ti]? with
      | some d => pure (some d.uid)
      | none => throw "攻撃対象が存在しない"
  let b := b.updMon c.active a.uid fun x => { x with attacked := true }
  return { b with attack := some ⟨a.uid, tu⟩ }

/-- ダメージ計算。攻撃モンスターや攻撃対象がいなくなっていれば攻撃は終了する。 -/
def performBattle (c : Ctx) (b : Board) : Board :=
  match b.attack with
  | none => b
  | some bt =>
    let b := { b with attack := none }
    let me := c.active
    let opp := c.active.other
    match (b.get me).monsters.find? (·.uid == bt.attacker) with
    | none => b
    | some a =>
      if a.pos ≠ .attack then b else
      let aAtk := b.atkOf me a
      match bt.target with
      | none => if (b.get opp).monsters.isEmpty then b.modify opp (·.damage aAtk) else b
      | some tu =>
        match (b.get opp).monsters.find? (·.uid == tu) with
        | none => b
        | some d =>
          -- 裏側守備表示は表側にしてからダメージ計算
          let flipped := d.pos = .faceDownDefense
          let d := if flipped then { d with pos := .faceUpDefense } else d
          let b := b.updMon opp tu fun _ => d
          let b := if flipped then { b with log := b.log ++ [⟨opp, d.card, .flipped, tu⟩] } else b
          let r := resolveBattle aAtk d.pos (b.atkOf opp d) d.card.dfs
          let b := (b.modify me (·.damage r.dmgToAttacker)).modify opp (·.damage r.dmgToDefender)
          let b := if r.attackerDestroyed then b.toGraveMon a.uid true else b
          if r.defenderDestroyed then b.toGraveMon tu true else b

def changePositionAct (c : Ctx) (b : Board) (i : Nat) : Except String Board := do
  unless c.phase.isMain do throw "表示形式の変更はメインフェイズのみ"
  let me := b.get c.active
  let some m := me.monsters[i]? | throw "モンスターが存在しない"
  if m.card.isLink then throw "リンクモンスターは守備表示にできない"
  if m.summonedTurn = c.turn then throw "召喚・セットしたターンは表示形式を変更できない"
  if m.posChanged || m.attacked then throw "このターン既に表示形式を変更したか攻撃している"
  let newPos ← match m.pos with
    | .attack => pure Position.faceUpDefense
    | .faceUpDefense => pure Position.attack
    | .faceDownDefense => throw "裏側守備表示は反転召喚で表にする"
  return b.updMon c.active m.uid fun x => { x with pos := newPos, posChanged := true }

def flipSummonAct (c : Ctx) (b : Board) (i : Nat) : Except String Board := do
  unless c.phase.isMain do throw "反転召喚はメインフェイズのみ"
  let me := b.get c.active
  let some m := me.monsters[i]? | throw "モンスターが存在しない"
  unless m.pos = .faceDownDefense do throw "裏側守備表示のモンスターではない"
  if m.summonedTurn = c.turn then throw "セットしたターンは反転召喚できない"
  if m.posChanged then throw "このターン既に表示形式を変更している"
  let b := b.updMon c.active m.uid fun x => { x with pos := .attack, posChanged := true }
  return { b with log := b.log ++ [⟨c.active, m.card, .flipped, m.uid⟩] }

def setSpellTrapAct (c : Ctx) (b : Board) (h : Nat) : Except String Board := do
  unless c.phase.isMain do throw "セットはメインフェイズのみ"
  let me := b.get c.active
  let some card := me.hand[h]? | throw "手札にそのカードがない"
  if let .monster _ := card then throw "モンスターは魔法・罠ゾーンにセットできない"
  unless me.backrow.length < spellTrapZones do throw "魔法・罠ゾーンに空きがない"
  return b.set c.active { me with hand := me.hand.eraseIdx h
                                  backrow := me.backrow ++ [{ card, setTurn := c.turn }] }

def discardAct (c : Ctx) (b : Board) (h : Nat) : Except String Board := do
  unless c.phase = .ending do throw "手札を捨てるのはエンドフェイズのみ"
  let me := b.get c.active
  unless me.hand.length > handLimit do throw "手札が上限を超えていない"
  let some card := me.hand[h]? | throw "手札にそのカードがない"
  return b.set c.active { me with hand := me.hand.eraseIdx h, grave := me.grave ++ [card] }

/-- ターンプレイヤーが空きチェーンで行う、チェーンに関わらない行動 -/
def boardAct (c : Ctx) (b : Board) : Action → Except String Board
  | .normalSummon h ts => summonCore c b h ts .attack
  | .normalSet h ts    => summonCore c b h ts .faceDownDefense
  | .flipSummon i      => flipSummonAct c b i
  | .changePosition i  => changePositionAct c b i
  | .extraSummon e ms  => extraSummonAct c b e ms
  | .setSpellTrap h    => setSpellTrapAct c b h
  | .attack a t        => declareAttack c b a t
  | .discard h         => discardAct c b h
  | _                  => throw "unreachable"

/-- パス。両者が続けてパスしたら、チェーンがあれば解決し、攻撃宣言中ならダメージ計算を行う。 -/
def passAct (c : Ctx) (s : ChainState) : ChainState :=
  if s.passed then
    if s.chain.isEmpty then { board := performBattle c s.board, priority := c.active }
    else { board := resolveChain c s.board false s.chain, priority := c.active }
  else { s with priority := s.priority.other, passed := true }

/-- 出来事に対応する誘発効果 -/
def triggeredLinks (h : Happened) : List ChainLink :=
  h.card.effects.filterMap fun
    | .trigger ev e =>
      if ev = h.ev then some { owner := h.who, card := .monster h.card, eff := e, speed := 1, mon := true, src := some h.uid }
      else none
    | _ => none

/-- チェーンが空なら、記録された出来事から誘発効果のチェーンを組む（ターンプレイヤーの効果が先） -/
def processTriggers (c : Ctx) (s : ChainState) : ChainState :=
  if !s.chain.isEmpty then s else
  let ls := s.board.log.flatMap triggeredLinks
  let b := { s.board with log := [] }
  if ls.isEmpty then { s with board := b }
  else { board := b, chain := (ls.filter (·.owner = c.active) ++ ls.filter (·.owner ≠ c.active)).reverse,
         priority := c.active, passed := false }

/-- フェイズ移行以外の行動 -/
def act (c : Ctx) (s : ChainState) : Action → Except String ChainState
  | .pass => pure (passAct c s)
  | .activateSpell h args => activateSpellAct c s h args
  | .activateSet who z args => activateSetAct c s who z args
  | .activateMonster who z i args => activateMonsterAct c s who z i args
  | a =>
    if !s.chain.isEmpty then throw "チェーンの処理中は発動とパスしか行えない"
    else if s.priority ≠ c.active then throw "優先権を持っていない"
    else if s.board.attack.isSome then throw "攻撃宣言中は発動とパスしか行えない"
    else (boardAct c s.board a).map fun b => { s with board := b, passed := false }

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
      let g' := { g with turn := g.turn + 1, active := nxt, phase := .draw, priority := nxt,
                         passed := false }
      match (b.get nxt).drawOne with
      | none   => pure { g' with board := b, result := some (.win g.active) }  -- デッキ切れ
      | some p => pure { g' with board := b.set nxt p }

def step (g : Game) (a : Action) : Except String Game :=
  if g.result.isSome then throw "既に決着がついている"
  else if a.isNextPhase then
    if g.chain.isEmpty ∧ g.board.attack.isNone ∧ g.priority = g.active then nextPhase g
    else throw "チェーンや攻撃の処理中、または優先権がないときはフェイズを進められない"
  else (act g.ctx g.cs a).map (fun s => checkResult (g.setCs (processTriggers g.ctx s)))

def play (g : Game) (as : List Action) : Except String Game :=
  as.foldlM step g

/-- 初期状態：互いに5枚ドローし、先攻1ターン目のドローフェイズから（先攻はドローしない） -/
def Game.init (d1 d2 : List Card) (e1 e2 : List Card := []) : Game where
  board := { p1 := { deck := d1.drop 5, hand := d1.take 5, extra := e1 },
             p2 := { deck := d2.drop 5, hand := d2.take 5, extra := e2 } }
  turn := 1
  active := .one
  phase := .draw

/-- 合法な手順で到達可能な状態 -/
inductive Reachable : Game → Prop
  | init (d1 d2 e1 e2 : List Card) : Reachable (Game.init d1 d2 e1 e2)
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

/-- **エクストラデッキのモンスターは通常召喚できない** -/
theorem extra_no_normal_summon (c : Ctx) (b b' : Board) (h : Nat) (ts : List Nat)
    (pos : Position) (m : MonsterCard) (hh : (b.get c.active).hand[h]? = some (.monster m))
    (hk : m.kind ≠ .main) : summonCore c b h ts pos ≠ .ok b' := by
  intro hok
  unfold summonCore at hok
  cases hm : c.phase.isMain <;> cases hs : b.normalSummoned <;>
    simp [hm, hs, hh, hk, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hok

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
  | init d1 d2 e1 e2 => simp [Inv, Game.init]
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

/-- 攻撃宣言はバトルフェイズでのみ成功する -/
theorem attack_requires_battle (c : Ctx) (b b' : Board) (i : Nat) (t : Option Nat)
    (h : declareAttack c b i t = .ok b') : c.phase = .battle := by
  unfold declareAttack at h
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
    cases hb : declareAttack g.ctx g.board i t with
    | error e =>
      simp only [act, boardAct, Game.cs, hb] at h
      repeat' split at h
      all_goals simp_all [Except.map, throw, throwThe, MonadExceptOf.throw]
    | ok b =>
      exact no_battle_first_turn g hr ht (attack_requires_battle g.ctx g.board b i t hb)

/-! ### 優先権とチェーンの定理 -/

/-- **優先権を持たないプレイヤーは発動できない** -/
theorem pushLink_priority (s s' : ChainState) (b : Board) (l : ChainLink)
    (h : pushLink s b l = .ok s') : l.owner = s.priority := by
  unfold pushLink at h
  by_cases h1 : l.owner = s.priority
  · exact h1
  · simp [h1, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h

/-- チェーンに積めるのは、スペルスピード2以上かつ直前のブロック以上のときだけ -/
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

/-- **空きチェーンでの召喚などはターンプレイヤーが優先権を持つときだけ** -/
theorem normalSummon_needs_priority (c : Ctx) (s s' : ChainState) (h : Nat) (ts : List Nat)
    (hok : act c s (.normalSummon h ts) = .ok s') :
    s.chain = [] ∧ s.priority = c.active := by
  simp only [act] at hok
  repeat' split at hok
  all_goals simp_all [Except.map, throw, throwThe, MonadExceptOf.throw]

/-- **チェーンは逆順に解決される**：無効化を含まないチェーンは、
最後に積まれたブロック（リストの先頭）から1つずつ解決される -/
theorem resolveChain_lifo (c : Ctx) (b : Board) (ls : List ChainLink)
    (hn : ∀ l ∈ ls, l.eff.isNegate = false) :
    resolveChain c b false ls = ls.foldl (resolveLink c) b := by
  induction ls generalizing b with
  | nil => rfl
  | cons l rest ih =>
    simp only [resolveChain, List.foldl, hn l (by simp), Bool.not_false, Bool.true_and,
      Bool.false_eq_true, ite_false]
    exact ih _ (fun x hx => hn x (by simp [hx]))

/-- **無効にされたブロックは効果を適用せずに墓地へ送られる** -/
theorem negated_link_skipped (c : Ctx) (b : Board) (n l : ChainLink) (rest : List ChainLink)
    (hn : n.eff.isNegate = true) :
    resolveChain c b false (n :: l :: rest) =
      resolveChain c (toGrave (resolveLink c b n) l) false rest := by
  simp [resolveChain, hn]

/-! ### 効果の無効化（スキルドレイン）の定理 -/

/-- **フィールドにいないモンスターの効果は、スキルドレインの適用下でも無効にならない**
（例：コストで自身をリリースした《ならず者傭兵部隊》、墓地で発動した《キラー・トマト》） -/
theorem effectNegated_offField (b : Board) (l : ChainLink) (h : l.src.bind b.findMon = none) :
    b.effectNegated l = false := by
  simp [Board.effectNegated, h]

/-- 無効化されていないモンスター効果は、そのまま処理される -/
theorem resolveLink_monster (c : Ctx) (b : Board) (l : ChainLink) (hm : l.mon = true)
    (hn : b.effectNegated l = false) : resolveLink c b l = applyEffect c l b := by
  simp [resolveLink, hm, hn]

/-- 無効化されたモンスター効果は何も起こさない -/
theorem resolveLink_negated (c : Ctx) (b : Board) (l : ChainLink) (hm : l.mon = true)
    (hn : b.effectNegated l = true) : resolveLink c b l = b := by
  simp [resolveLink, hm, hn]

/-! ### エクストラデッキの定理 -/

/-- シンクロ素材のチューナーはちょうど1体 -/
theorem synchroOk_one_tuner (em : MonsterCard) (ms : List MonsterCard) (h : synchroOk em ms) :
    (ms.filter (·.tuner)).length = 1 := by
  simp [synchroOk] at h
  exact h.1.1.1

/-- シンクロ素材のレベルの合計はシンクロモンスターのレベルに等しい -/
theorem synchroOk_level_sum (em : MonsterCard) (ms : List MonsterCard) (h : synchroOk em ms) :
    (ms.map (·.level?.getD 0)).sum = em.level := by
  simp [synchroOk] at h
  exact h.2

/-- エクシーズ素材はすべてランクと同じレベルを持つ（エクシーズ・リンクは素材にできない） -/
theorem xyzOk_levels (n r : Nat) (ms : List MonsterCard) (h : xyzOk n r ms) :
    ∀ m ∈ ms, m.level? = some r := by
  simp [xyzOk] at h
  exact h.2

/-- リンクモンスターを含まない素材は、1体につき1として数える -/
theorem linkSums_plain (ms : List MonsterCard) (h : ∀ m ∈ ms, m.isLink = false) :
    linkSums ms = [ms.length] := by
  induction ms with
  | nil => rfl
  | cons m rest ih =>
    have hm := h m (by simp)
    have ih := ih (fun x hx => h x (by simp [hx]))
    simp only [linkSums, List.foldr] at ih ⊢
    rw [ih]
    cases hk : m.kind <;> simp_all [MonsterCard.isLink]

/-- リンクモンスターを含まなければ、素材の数がリンクマーカーの数と等しいときだけリンク召喚できる -/
theorem linkOk_plain (r : Nat) (ms : List MonsterCard) (h : ∀ m ∈ ms, m.isLink = false) :
    linkOk r ms = true ↔ ms.length = r := by
  simp [linkOk, linkSums_plain ms h]
  omega

end Theorems

/-! ## 9. カード例 -/

namespace Cards

-- メインデッキのモンスター
def blueEyes       : MonsterCard := ⟨"青眼の白龍", 8, 3000, 2500, .light, .dragon, .main, false, []⟩
def darkMagician   : MonsterCard := ⟨"ブラック・マジシャン", 7, 2500, 2100, .dark, .spellcaster, .main, false, []⟩
def redEyes        : MonsterCard := ⟨"真紅眼の黒竜", 7, 2400, 2000, .dark, .dragon, .main, false, []⟩
def summonedSkull  : MonsterCard := ⟨"デーモンの召喚", 6, 2500, 1200, .dark, .fiend, .main, false, []⟩
def celticGuardian : MonsterCard := ⟨"エルフの剣士", 4, 1400, 1200, .earth, .warrior, .main, false, []⟩
def giantSoldier   : MonsterCard := ⟨"岩石の巨兵", 3, 1300, 2000, .earth, .rock, .main, false, []⟩
def mysticalElf    : MonsterCard := ⟨"ホーリー・エルフ", 4, 800, 2000, .light, .spellcaster, .main, false, []⟩
def kuriboh        : MonsterCard := ⟨"クリボー", 1, 300, 200, .dark, .fiend, .main, false, []⟩  -- 効果は省略
def tuneWarrior    : MonsterCard := ⟨"チューン・ウォリアー", 3, 1600, 200, .earth, .warrior, .main, true, []⟩

-- 効果モンスター
/-- 永続効果：自分の戦士族モンスターの攻撃力400アップ（攻撃対象にならない効果は省略） -/
def commandKnight : MonsterCard :=
  { name := "コマンド・ナイト", level := 4, atk := 1200, dfs := 1900, attr := .fire, race := .warrior,
    effects := [.continuous (.atkUpOwn (some .warrior) 400)] }
/-- 起動効果：このカードをリリースし、フィールドのモンスター1体を対象として破壊する -/
def exiledForce : MonsterCard :=
  { name := "ならず者傭兵部隊", level := 4, atk := 1000, dfs := 1000, attr := .earth, race := .warrior,
    effects := [.ignition .tributeSelf .destroyTarget] }
/-- リバース：相手のデッキの上から5枚を墓地へ送る -/
def needleWorm : MonsterCard :=
  { name := "ニードル・ワーム", level := 2, atk := 750, dfs := 600, attr := .earth, race := .insect,
    effects := [.trigger .flipped (.millOpp 5)] }
/-- 戦闘で破壊され墓地へ送られた時：デッキから攻撃力1500以下の闇属性モンスターを特殊召喚 -/
def killerTomato : MonsterCard :=
  { name := "キラー・トマト", level := 4, atk := 1400, dfs := 1100, attr := .dark, race := .plant,
    effects := [.trigger .destroyedByBattle (.recruit .dark 1500)] }
/-- 戦闘で破壊され墓地へ送られた時：デッキから攻撃力1500以下の地属性モンスターを特殊召喚 -/
def giantRat : MonsterCard :=
  { name := "巨大ネズミ", level := 4, atk := 1400, dfs := 1450, attr := .earth, race := .beast,
    effects := [.trigger .destroyedByBattle (.recruit .earth 1500)] }
/-- フィールドから墓地へ送られた場合：デッキから守備力1500以下のモンスターを手札に加える -/
def witch : MonsterCard :=
  { name := "黒き森のウィッチ", level := 4, atk := 1100, dfs := 1200, attr := .dark, race := .spellcaster,
    effects := [.trigger .sentToGraveFromField (.searchMaxDef 1500)] }
/-- 特殊召喚に成功した時：自分は1枚ドローする -/
def sacredCrane : MonsterCard :=
  { name := "聖鳥クレイン", level := 4, atk := 1600, dfs := 400, attr := .light, race := .wingedBeast,
    effects := [.trigger .specialSummoned (.draw 1)] }

-- エクストラデッキのモンスター
def bSkullDragon : MonsterCard :=
  { name := "ブラック・デーモンズ・ドラゴン", level := 9, atk := 3200, dfs := 2500, attr := .dark,
    race := .dragon, kind := .fusion ["真紅眼の黒竜", "デーモンの召喚"] }
def gaiaKnight : MonsterCard :=
  { name := "大地の騎士ガイアナイト", level := 6, atk := 2600, dfs := 800, attr := .earth,
    race := .warrior, kind := .synchro }
/-- X素材を1つ取り除き、相手モンスターの攻撃を無効にする（X素材がない時の自壊は省略） -/
def hope : MonsterCard :=
  { name := "No.39 希望皇ホープ", level := 4, atk := 2500, dfs := 2000, attr := .light,
    race := .warrior, kind := .xyz 2, effects := [.quick (.detach 1) .negateAttack] }
/-- リンク2、素材はモンスター2体（身代わりの効果は省略） -/
def proxyDragon : MonsterCard :=
  { name := "プロキシー・ドラゴン", level := 0, atk := 1400, dfs := 0, attr := .dark,
    race := .cyberse, kind := .link 2 }

-- 魔法
def potOfGreed   : Card := .spell "強欲な壺" (.normal (.draw 2))
def raigeki      : Card := .spell "サンダー・ボルト" (.normal .destroyOppMonsters)
def darkHole     : Card := .spell "ブラック・ホール" (.normal .destroyAllMonsters)
def hinotama     : Card := .spell "火の粉" (.normal (.burn 500))
def ookazi       : Card := .spell "昼夜の大火事" (.normal (.burn 800))
def dianKeto     : Card := .spell "治療の神 ディアン・ケト" (.normal (.heal 1000))
def monsterReborn : Card := .spell "死者蘇生" (.normal .revive)
def polymerization : Card := .spell "融合" (.normal .fusionSummon)
def axeOfDespair : Card := .spell "デーモンの斧" (.equip 1000)
def burdenOfMighty : Card := .spell "強者の苦痛" (.continuous (.oppAtkDownPerLevel 100))

-- 罠
def justDesserts : Card := .trap "仕込みマシンガン" (.normal (.burnPerOppMonster 500))
def darkBribe    : Card := .trap "魔宮の賄賂" (.counter (.negate 1))
def sakuretsu    : Card := .trap "炸裂装甲" (.normal .destroyAttacker)
def gravityBind  : Card := .trap "グラヴィティ・バインド－超重力の網－" (.continuous (.noAttackLevelGE 4))
def skillDrain   : Card := .trap "スキルドレイン" (.continuous .negateMonsterEffects (.payLP 1000))

end Cards

/-! ## 10. 対戦例 -/

namespace Demo
open Cards

def np : Action := .nextPhase

/-- 発動（または攻撃宣言）して両者がパスし、チェーン（またはダメージ計算）を処理する -/
def resolve (a : Action) : List Action := [a, .pass, .pass]

def names (ms : List FieldMonster) : List String := ms.map (·.card.name)

/-- フィールドのモンスター（盤面を直接作る例用） -/
def fm (uid : Nat) (c : MonsterCard) (pos : Position := .attack) (turn : Nat := 1)
    (overlays : List Card := []) : FieldMonster :=
  { uid, card := c, pos, summonedTurn := turn, overlays }

/-! ### 通常の対戦 -/

def deck1 : List Card :=
  [.monster celticGuardian, .monster giantSoldier, potOfGreed, raigeki, hinotama,
   .monster summonedSkull, .monster darkMagician, .monster blueEyes, ookazi]

def deck2 : List Card :=
  [.monster mysticalElf, .monster kuriboh, justDesserts, dianKeto, .monster giantSoldier,
   darkHole, .monster kuriboh]

def script : List Action :=
  -- ターン1（先攻・P1）：ドローなし、エルフの剣士を召喚。バトルフェイズは飛ばされる
  [np, np, .normalSummon 0 [], np, np] ++
  -- ターン2（P2）：ホーリー・エルフを裏守備、仕込みマシンガンをセット
  [np, np, .normalSet 0 [], .setSpellTrap 1, np, np, np, np] ++
  -- ターン3（P1）：強欲な壺 → サンダー・ボルト → エルフの剣士をリリースしてデーモンの召喚
  [np, np] ++ resolve (.activateSpell 1) ++ resolve (.activateSpell 1) ++ [.normalSummon 2 [0]] ++
  [.pass] ++ resolve (.activateSet .two 0) ++  -- P1 が優先権を渡し、P2 が仕込みマシンガン（500×1）
  [np] ++ resolve (.attack 0 none) ++           -- デーモンの召喚で直接攻撃 2500
  [np] ++ resolve (.activateSpell 1) ++ [np, np] ++ -- 火の粉 500
  -- ターン4（P2）：ブラック・ホール → 岩石の巨兵で直接攻撃 → ディアン・ケト
  [np, np] ++ resolve (.activateSpell 3) ++ [.normalSummon 2 [], np] ++ resolve (.attack 0 none) ++
  [np] ++ resolve (.activateSpell 1) ++ [np, np] ++
  -- ターン5（P1）：昼夜の大火事、岩石の巨兵同士で相打ち
  [np, np] ++ resolve (.activateSpell 3) ++ [.normalSummon 0 [], np] ++ resolve (.attack 0 (some 0)) ++
  [np, np, np]
  -- ターン6 のドローで P2 はデッキ切れ → P1 の勝利

def final : Except String Game := play (Game.init deck1 deck2) script

#eval final.map (fun g => (g.turn, g.board.p1.lp, g.board.p2.lp, g.result))

/-- この対戦は P1 のデッキ切れ勝ちで終わる（カーネルで検証） -/
example : (final.toOption.bind (·.result)) = some (.win .one) := by decide

-- 反則の例
#eval (play (Game.init deck1 deck2) [np, np, np, np]).map (fun g => (g.turn, g.active, g.board.p2.hand.length))
#eval (play (Game.init deck1 deck2) [np, np, .normalSummon 0 [], .normalSummon 0 []]).map (·.turn)
#eval (play (Game.init deck1 deck2) [np, np, np, .attack 0 none]).map (·.turn)

/-! ### チェーンと優先権
P1 のメインフェイズ1。P1 は手札に昼夜の大火事、魔宮の賄賂をセット済み。
P2 は仕込みマシンガンをセット済み。P1 の場にはエルフの剣士が1体。 -/

def chainStart : Game where
  board := { p1 := { deck := [], hand := [ookazi], monsters := [fm 0 celticGuardian],
                     backrow := [{ card := darkBribe, setTurn := 1 }] },
             p2 := { deck := [.monster kuriboh], backrow := [{ card := justDesserts, setTurn := 2 }] },
             nextUid := 1 }
  turn := 3
  active := .one
  phase := .main1

/-- C1 昼夜の大火事 → C2 仕込みマシンガン → C3 魔宮の賄賂 → 両者パス
解決は逆順：C3 で P2 が1枚ドローし C2 を無効、C2 は不発で墓地へ、C1 で P2 に 800 -/
def chainEnd : Except String Game :=
  play chainStart [.activateSpell 0, .activateSet .two 0, .activateSet .one 0, .pass, .pass]

#eval chainEnd.map (fun g => (g.board.p1.lp, g.board.p2.lp, g.board.p2.hand.length, g.chain.length))

/-- 仕込みマシンガンは無効にされ、P1 は無傷。P2 は 800 ダメージを受けて1枚ドロー -/
example : chainEnd.toOption.map (fun g => (g.board.p1.lp, g.board.p2.lp, g.board.p2.hand.length))
    = some (8000, 7200, 1) := by decide

-- 優先権：P1 がパスするまで P2 は発動できない
#eval (play chainStart [.activateSet .two 0]).map (fun _ => ())
#eval (play chainStart [.pass, .activateSet .two 0, .pass, .pass]).map (fun g => g.board.p1.lp)
-- 反則の例：チェーン中のフェイズ移行、スペルスピード1のチェーン、カウンター罠への通常罠
#eval (play chainStart [.activateSpell 0, .nextPhase]).map (fun _ => ())
#eval (play { chainStart with board := (chainStart.board.modify .one
              (fun p => { p with hand := [ookazi, hinotama] })) }
        [.activateSpell 0, .pass, .activateSpell 0]).map (fun _ => ())
#eval (play { chainStart with board := (chainStart.board.modify .two
              (fun p => { p with backrow := [{ card := justDesserts, setTurn := 2 },
                                             { card := justDesserts, setTurn := 2 }] })) }
        [.activateSpell 0, .activateSet .two 0, .activateSet .one 0, .activateSet .two 0]).map
        (fun _ => ())

/-! ### 融合召喚
手札の真紅眼の黒竜とフィールドのデーモンの召喚を素材に、ブラック・デーモンズ・ドラゴンを融合召喚 -/

def fusionStart : Game where
  board := { p1 := { deck := [], hand := [polymerization, .monster redEyes],
                     monsters := [fm 0 summonedSkull], extra := [.monster bSkullDragon] },
             p2 := { deck := [] }, nextUid := 1 }
  turn := 3
  active := .one
  phase := .main1

def fusionEnd : Except String Game :=
  play fusionStart (resolve (.activateSpell 0 { hand := [1], mine := [0], extra := some 0 }))

#eval fusionEnd.map (fun g => (names g.board.p1.monsters, g.board.p1.grave.map (·.name)))

example : fusionEnd.toOption.map (fun g => (names g.board.p1.monsters, g.board.p1.grave.length,
    g.board.p1.extra.length)) = some (["ブラック・デーモンズ・ドラゴン"], 3, 0) := by decide

-- 素材が足りなければ発動できない
#eval (play fusionStart [.activateSpell 0 { mine := [0], extra := some 0 }]).map (fun _ => ())

/-! ### シンクロ召喚
チューン・ウォリアー（レベル3チューナー）＋岩石の巨兵（レベル3）→ 大地の騎士ガイアナイト（レベル6） -/

def synchroStart : Game where
  board := { p1 := { deck := [], monsters := [fm 0 tuneWarrior, fm 1 giantSoldier, fm 2 celticGuardian],
                     extra := [.monster gaiaKnight] },
             p2 := { deck := [] }, nextUid := 3 }
  turn := 3
  active := .one
  phase := .main1

#eval (play synchroStart [.extraSummon 0 [0, 1]]).map (fun g => names g.board.p1.monsters)

example : (play synchroStart [.extraSummon 0 [0, 1]]).toOption.map (fun g => names g.board.p1.monsters)
    = some ["エルフの剣士", "大地の騎士ガイアナイト"] := by decide

-- レベルの合計が合わない（3 + 4 = 7）
#eval (play synchroStart [.extraSummon 0 [0, 2]]).map (fun _ => ())

/-! ### エクシーズ召喚と誘発即時効果
レベル4の2体で No.39 希望皇ホープ。相手ターンの攻撃宣言時に X素材を1つ取り除いて攻撃を無効にする。 -/

def xyzStart : Game where
  board := { p1 := { deck := [], monsters := [fm 0 celticGuardian, fm 1 mysticalElf .faceUpDefense],
                     extra := [.monster hope] },
             p2 := { deck := [] }, nextUid := 2 }
  turn := 3
  active := .one
  phase := .main1

#eval (play xyzStart [.extraSummon 0 [0, 1]]).map
  (fun g => (names g.board.p1.monsters, g.board.p1.monsters.map (·.overlays.length)))

/-- P2 のバトルフェイズ。青眼の白龍がホープに攻撃宣言 -/
def hopeDefense : Game where
  board := { p1 := { deck := [], monsters := [fm 0 hope .attack 3 [.monster celticGuardian, .monster mysticalElf]],
                     backrow := [{ card := sakuretsu, setTurn := 3 }] },
             p2 := { deck := [], monsters := [fm 1 blueEyes .attack 2] }, nextUid := 2 }
  turn := 4
  active := .two
  phase := .battle
  priority := .two

-- ホープの効果で攻撃を無効にする（P2 がパスして P1 に優先権が移ってから発動）
def hopeEnd : Except String Game :=
  play hopeDefense ([.attack 0 (some 0), .pass, .activateMonster .one 0, .pass, .pass])

#eval hopeEnd.map (fun g => (g.board.p1.lp, names g.board.p1.monsters,
  g.board.p1.monsters.map (·.overlays.length), g.board.attack.isSome))

example : hopeEnd.toOption.map (fun g => (g.board.p1.lp, g.board.p1.monsters.map (·.overlays.length)))
    = some (8000, [1]) := by decide

-- 炸裂装甲で攻撃モンスターを破壊する
#eval (play hopeDefense [.attack 0 (some 0), .pass, .activateSet .one 0, .pass, .pass]).map
  (fun g => (names g.board.p2.monsters, g.board.p2.grave.map (·.name)))

/-! ### リンク召喚
モンスター2体でプロキシー・ドラゴン（エクストラモンスターゾーンへ）。
エクストラモンスターゾーンが埋まっていると、2体目のリンクモンスターは出せない。 -/

def linkStart : Game where
  board := { p1 := { deck := [], monsters := [fm 0 celticGuardian, fm 1 kuriboh, fm 2 giantSoldier,
                                               fm 3 mysticalElf],
                     extra := [.monster proxyDragon, .monster proxyDragon] },
             p2 := { deck := [] }, nextUid := 4 }
  turn := 3
  active := .one
  phase := .main1

#eval (play linkStart [.extraSummon 0 [0, 1]]).map
  (fun g => g.board.p1.monsters.map (fun m => (m.card.name, m.emz)))
#eval (play linkStart [.extraSummon 0 [0, 1], .extraSummon 0 [0, 1]]).map (fun _ => ())

/-! ### 誘発効果 -/

/-- P2 の青眼の白龍がキラー・トマトに攻撃。戦闘破壊されたトマトの効果で黒き森のウィッチを特殊召喚 -/
def tomatoStart : Game where
  board := { p1 := { deck := [.monster blueEyes, .monster witch, .monster kuriboh],
                     monsters := [fm 0 killerTomato .attack 3] },
             p2 := { deck := [], monsters := [fm 1 blueEyes .attack 2] }, nextUid := 2 }
  turn := 4
  active := .two
  phase := .battle
  priority := .two

-- 攻撃宣言 → 両者パスでダメージ計算 → 誘発効果のチェーン → 両者パスで解決
def tomatoEnd : Except String Game :=
  play tomatoStart (resolve (.attack 0 (some 0)) ++ [.pass, .pass])

#eval tomatoEnd.map (fun g => (g.board.p1.lp, names g.board.p1.monsters, g.board.p1.deck.length))

example : tomatoEnd.toOption.map (fun g => (g.board.p1.lp, names g.board.p1.monsters))
    = some (6400, ["黒き森のウィッチ"]) := by decide

/-- 裏側守備表示のニードル・ワームを攻撃するとリバースし、相手のデッキを5枚墓地へ送る -/
def wormStart : Game where
  board := { p1 := { deck := [], monsters := [fm 0 needleWorm .faceDownDefense 3] },
             p2 := { deck := List.replicate 6 (.monster kuriboh), monsters := [fm 1 blueEyes .attack 2] },
             nextUid := 2 }
  turn := 4
  active := .two
  phase := .battle
  priority := .two

#eval (play wormStart (resolve (.attack 0 (some 0)) ++ [.pass, .pass])).map
  (fun g => (g.board.p1.monsters.length, g.board.p2.deck.length, g.board.p2.grave.length))

/-- ならず者傭兵部隊（自身をリリースして破壊）で黒き森のウィッチを破壊 → ウィッチの効果でクリボーをサーチ -/
def exiledStart : Game where
  board := { p1 := { deck := [], monsters := [fm 0 exiledForce] },
             p2 := { deck := [.monster giantSoldier, .monster kuriboh], monsters := [fm 1 witch .attack 2] },
             nextUid := 2 }
  turn := 3
  active := .one
  phase := .main1

def exiledEnd : Except String Game :=
  play exiledStart (resolve (.activateMonster .one 0 0 { targets := [(.two, 0)] }) ++ [.pass, .pass])

#eval exiledEnd.map (fun g => (g.board.p1.monsters.length, g.board.p2.monsters.length,
  g.board.p2.hand.map (·.name)))

example : exiledEnd.toOption.map (fun g => g.board.p2.hand.map (·.name)) = some ["クリボー"] := by
  decide

/-- 死者蘇生で聖鳥クレインを特殊召喚 → クレインの効果で1枚ドロー -/
def rebornStart : Game where
  board := { p1 := { deck := [.monster kuriboh], hand := [monsterReborn], grave := [.monster sacredCrane] },
             p2 := { deck := [] } }
  turn := 3
  active := .one
  phase := .main1

#eval (play rebornStart (resolve (.activateSpell 0 { grave := some (.one, 0) }) ++ [.pass, .pass])).map
  (fun g => (names g.board.p1.monsters, g.board.p1.hand.map (·.name)))

/-! ### 永続効果・装備魔法 -/

/-- コマンド・ナイトの永続効果（戦士族+400）、デーモンの斧（+1000）、相手の強者の苦痛（レベル×100ダウン） -/
def auraStart : Game where
  board := { p1 := { deck := [], hand := [axeOfDespair],
                     monsters := [fm 0 commandKnight, fm 1 celticGuardian] },
             p2 := { deck := [], backrow := [{ card := burdenOfMighty, setTurn := 2, faceUp := true }] },
             nextUid := 2 }
  turn := 3
  active := .one
  phase := .main1

def auraEnd : Except String Game :=
  play auraStart (resolve (.activateSpell 0 { targets := [(.one, 1)] }))

-- コマンド・ナイト 1200+400-400 = 1200、エルフの剣士 1400+400+1000-400 = 2400
#eval auraEnd.map (fun g => g.board.p1.monsters.map (g.board.atkOf .one ·))

example : auraEnd.toOption.map (fun g => g.board.p1.monsters.map (g.board.atkOf .one ·))
    = some [1200, 2400] := by decide

-- 装備モンスターがフィールドを離れると装備カードも墓地へ送られる
#eval (auraEnd.map fun g => g.board.toGraveMon 1).map
  (fun b => (b.p1.backrow.length, b.p1.grave.map (·.name)))

/-- グラヴィティ・バインド：レベル4以上は攻撃できないが、ランクを持つホープは攻撃できる -/
def gravityStart : Game where
  board := { p1 := { deck := [], backrow := [{ card := gravityBind, setTurn := 1, faceUp := true }] },
             p2 := { deck := [], monsters := [fm 0 blueEyes .attack 2, fm 1 hope .attack 2] }, nextUid := 2 }
  turn := 4
  active := .two
  phase := .battle
  priority := .two

#eval (play gravityStart [.attack 0 none]).map (fun _ => ())
#eval (play gravityStart (resolve (.attack 1 none))).map (fun g => g.board.p1.lp)

/-! ### スキルドレイン
フィールドの表側表示モンスターの効果を無効にする。無効になるのは、処理時にフィールドに
表側表示で存在するモンスターの効果だけ。 -/

/-- 相手（P2）がスキルドレインを発動済み（LP 1000 を払っている） -/
def withDrain (g : Game) : Game :=
  { g with board := g.board.modify .two fun p =>
      { p with lp := p.lp - 1000, backrow := p.backrow ++ [{ card := skillDrain, setTurn := 2, faceUp := true }] } }

/-- 《ならず者傭兵部隊》は自身をリリースして発動するので、処理時にはフィールドにいない。
効果は無効にならず、相手モンスターを破壊できる。墓地へ送られたウィッチの効果も墓地で処理される。 -/
def drainExiledEnd : Except String Game :=
  play (withDrain exiledStart)
    (resolve (.activateMonster .one 0 0 { targets := [(.two, 0)] }) ++ [.pass, .pass])

#eval drainExiledEnd.map (fun g => (names g.board.p2.monsters, g.board.p2.hand.map (·.name)))

example : drainExiledEnd.toOption.map (fun g => (names g.board.p2.monsters, g.board.p2.hand.map (·.name)))
    = some ([], ["クリボー"]) := by decide

/-- ホープはフィールドで効果を処理するので無効になる（発動はでき、X素材は取り除かれる）。
攻撃は続き、ホープは戦闘で破壊される。 -/
def drainHopeEnd : Except String Game :=
  play (withDrain hopeDefense)
    ([.attack 0 (some 0), .pass, .activateMonster .one 0, .pass, .pass] ++ [.pass, .pass])

#eval drainHopeEnd.map (fun g => (g.board.p1.lp, names g.board.p1.monsters, g.board.p1.grave.length))

example : drainHopeEnd.toOption.map (fun g => (g.board.p1.lp, names g.board.p1.monsters))
    = some (7500, []) := by decide

-- 永続効果も無効になる：コマンド・ナイトの攻撃力アップが消える（強者の苦痛の -400 のみ）
#eval (withDrain auraStart).board.p1.monsters.map ((withDrain auraStart).board.atkOf .one ·)

/-- LP がちょうど 1000 のときはスキルドレインを発動できない（LP が 0 以下になるようには払えない） -/
def drainCostStart (lp : Nat) : Game where
  board := { p1 := { deck := [] },
             p2 := { deck := [], lp, backrow := [{ card := skillDrain, setTurn := 2 }] } }
  turn := 3
  active := .one
  phase := .main1

#eval (play (drainCostStart 1000) [.pass, .activateSet .two 0]).map (fun _ => ())
#eval (play (drainCostStart 1001) (.pass :: resolve (.activateSet .two 0))).map (fun g => g.board.p2.lp)

example : (play (drainCostStart 1000) [.pass, .activateSet .two 0]).toOption.isNone := by decide

-- 戦闘で破壊され墓地へ送られた《キラー・トマト》の効果は墓地で処理されるので無効にならない
#eval (play (withDrain tomatoStart) (resolve (.attack 0 (some 0)) ++ [.pass, .pass])).map
  (fun g => names g.board.p1.monsters)

end Demo

end YGO
