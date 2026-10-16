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
* 罠の封殺（サイコ・ショッカー、王宮のお触れ）：罠の発動の禁止、フィールドの罠の効果の無効化
* 永続効果どうしの無効化は適用が始まった順番（タイムスタンプ）で判定する：
  一方的に無効にする効果は順番に関係なく優先され、互いに無効にし合う効果は先に適用された方が優先される。
  無効にしている側が無効化されれば、無効にされていた側は有効に戻り、その時点で新たに適用されたものとして扱う。
  有効・無効は前回の判定結果から1つずつ順に変わるので（スキルドレイン・サイコ・ショッカー・王宮のお触れの
  3すくみ）、判定結果は1手ごとに盤面に書き込む。
  処理は1つずつ順番に行われるので、2枚が同じ時刻に適用され始めることはない
* 対象と関係を持つ永続罠（リビングデッドの呼び声）：このカードが離れた時、または蘇生したモンスターが
  破壊された時にもう一方を破壊する（その時点で効果が無効なら何も起きない）
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
  | revive (ownOnly : Bool := false) -- 対象の墓地のモンスター1体を自分フィールドに特殊召喚（ownOnly なら自分の墓地のみ）
  | fusionSummon                 -- 手札・フィールドの素材を墓地へ送り融合召喚
  | destroyAttacker              -- 攻撃してきた相手モンスターを破壊
  | destroyOppSpellTraps         -- 相手の魔法・罠ゾーンのカードを全て破壊
  | destroyAllSpellTraps         -- フィールドの魔法・罠カードを全て破壊
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
  | noTrapActivation                        -- お互いに罠カードを発動できない
  | negateTraps                             -- （このカード以外の）フィールドの罠カードの効果を無効にする
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
  | continuous (auras : List Aura) (cost : Cost := .free) (e : Effect := .noop) (bond : Bool := false)
    -- bond：発動時の効果で特殊召喚したモンスターと関係を持つ
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
  | .trap _ (.continuous _ _ e _) => e
  | _ => .noop

/-- 表側表示で魔法・罠ゾーンにある間、適用され続ける効果 -/
def Card.auras : Card → List Aura
  | .spell _ (.continuous a) => [a]
  | .trap _ (.continuous as ..) => as
  | _ => []

/-- 発動時に払う LP -/
def Card.lpCost : Card → Nat
  | .trap _ (.continuous _ (.payLP n) ..) => n
  | _ => 0

def Card.isTrap : Card → Bool
  | .trap .. => true
  | _ => false

/-- 特殊召喚したモンスターと関係を持つ永続罠か -/
def Card.bonds : Card → Bool
  | .trap _ (.continuous _ _ _ b) => b
  | _ => false

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
  since        : Nat := 0       -- 効果が適用された時刻（永続効果の適用順）
  negated      : Bool := false  -- 前回の判定で永続効果が無効化されていた
  deriving Repr, DecidableEq

/-- 魔法・罠ゾーンのカード -/
structure SetCard where
  card    : Card
  setTurn : Nat
  faceUp  : Bool := false        -- 表側表示（発動済みの永続・装備カード）
  equipTo : Option Nat := none   -- 装備しているモンスターの uid
  bond    : Option Nat := none   -- 関係を持つモンスターの uid（リビングデッドの呼び声）
  since   : Nat := 0             -- 効果が適用された時刻（永続効果の適用順）
  negated : Bool := false        -- 前回の判定で永続効果が無効化されていた
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

def PlayerId.code : PlayerId → Nat
  | .one => 1
  | .two => 2

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

/-- モンスターがフィールドを離れる理由 -/
inductive LeaveCause where
  | sent        -- リリース・素材・コストなど（破壊ではない）
  | destroyed   -- 効果による破壊
  | battle      -- 戦闘による破壊
  deriving Repr, DecidableEq

/-- 盤面：ターン・フェイズに依存しない部分 -/
structure Board where
  p1 : Player
  p2 : Player
  normalSummoned : Bool := false
  nextUid : Nat := 0
  clock   : Nat := 0             -- 永続効果の適用順を決める時刻
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

end Player

/-! ### 永続効果の適用順 -/

inductive SrcKind where
  | spell | trap | monster
  deriving Repr, DecidableEq

/-- 永続効果を持ちうる表側表示のカード -/
structure AuraSrc where
  who   : PlayerId
  kind  : SrcKind
  key   : Nat × Nat × Nat   -- カードの識別（同じカードかどうか）
  since : Nat               -- 効果が適用された時刻（無効から有効に戻った場合は戻った時刻）
  on    : Bool              -- 効果が適用されている（無効化されていない）
  auras : List Aura
  deriving Repr, DecidableEq

/-- t の永続効果が s の効果を無効にするか（自分自身は無効にしない） -/
def AuraSrc.negates (t s : AuraSrc) : Bool :=
  t.key != s.key && t.auras.any fun a =>
    match a, s.kind with
    | .negateMonsterEffects, .monster => true
    | .negateTraps, .trap => true
    | _, _ => false

/-- t が s を無効にする。互いに無効にし合う場合は、先に適用された方だけが無効にする。
処理は1つずつ順番に行われるので、2枚が同じ時刻に適用されることはない（`play` で進める限り、
表側表示になるたび・無効から有効に戻るたびに `Board.clock` が進む）。盤面を直接作る場合は
`since` が重ならないようにする。 -/
def AuraSrc.beats (t s : AuraSrc) : Bool :=
  t.negates s && !(s.negates t && s.since < t.since)

/-- s を無効にする、適用中のカードがあるか -/
def beatenIn (srcs : List AuraSrc) (s : AuraSrc) : Bool :=
  srcs.any fun t => t.on && t.beats s

/-- 永続効果の有効・無効を1つだけ変える。
* 適用中のカードを無効にする適用中のカードがあれば、そのカードを無効にする
* なければ、どの適用中のカードにも無効にされない無効なカードを、新しい時刻で有効に戻す
* どちらもなければ、状態は決まっている（`none`）

有効に戻ったカードは「その時点で新たに適用された」ので、互いに無効にし合う相手が先に適用中なら
すぐにまた無効になる（スキルドレイン → サイコ・ショッカー → 王宮のお触れの3すくみ）。 -/
def settleOnce (srcs : List AuraSrc) (clock : Nat) : Option (List AuraSrc × Nat) :=
  match srcs.findIdx? (fun s => s.on && beatenIn srcs s) with
  | some i => some (srcs.modify i ({ · with on := false }), clock)
  | none =>
    match srcs.findIdx? (fun s => !s.on && !beatenIn srcs s) with
    | some i => some (srcs.modify i ({ · with on := true, since := clock + 1 }), clock + 1)
    | none => none

def settleAux : Nat → List AuraSrc → Nat → List AuraSrc × Nat
  | 0, srcs, c => (srcs, c)
  | n + 1, srcs, c =>
    match settleOnce srcs c with
    | some (srcs', c') => settleAux n srcs' c'
    | none => (srcs, c)

/-- 状態が決まるまで `settleOnce` を繰り返す（回数の上限は念のため） -/
def settle (srcs : List AuraSrc) (clock : Nat) : List AuraSrc × Nat :=
  settleAux (4 * (srcs.length + 1) ^ 2) srcs clock

/-- 無効化されていないカード -/
def effectiveSources (srcs : List AuraSrc) (clock : Nat) : List AuraSrc :=
  (settle srcs clock).1.filter (·.on)

/-- 魔法・罠ゾーンの i 番目のカードの識別 -/
def stKey (w : PlayerId) (i : Nat) : Nat × Nat × Nat := (1, w.code, i)

/-- モンスターの識別 -/
def monKey (uid : Nat) : Nat × Nat × Nat := (0, 0, uid)

def Player.sources (p : Player) (w : PlayerId) : List AuraSrc :=
  ((List.range p.backrow.length).filterMap fun i =>
    match p.backrow[i]? with
    | some s =>
      if s.faceUp then
        some { who := w, kind := if s.card.isTrap then .trap else .spell, key := stKey w i,
               since := s.since, on := !s.negated, auras := s.card.auras }
      else none
    | none => none) ++
  p.monsters.filterMap fun m =>
    if m.pos = .faceDownDefense then none
    else some { who := w, kind := .monster, key := monKey m.uid, since := m.since, on := !m.negated,
                auras := m.card.effects.filterMap MonsterEffect.aura? }

namespace Board

def findMon (b : Board) (uid : Nat) : Option (PlayerId × FieldMonster) :=
  match b.p1.monsters.find? (·.uid == uid) with
  | some m => some (.one, m)
  | none => (b.p2.monsters.find? (·.uid == uid)).map (.two, ·)

def updMon (b : Board) (w : PlayerId) (uid : Nat) (f : FieldMonster → FieldMonster) : Board :=
  b.modify w fun p => { p with monsters := p.monsters.map fun m => if m.uid = uid then f m else m }

def sources (b : Board) : List AuraSrc := b.p1.sources .one ++ b.p2.sources .two

/-- 無効化されていないカード -/
def effective (b : Board) : List AuraSrc := effectiveSources b.sources b.clock

/-- 適用中の永続効果とそのコントローラー。前回書き込んだ判定結果とその時点の盤面から計算する。 -/
def auras (b : Board) : List (PlayerId × Aura) :=
  b.effective.flatMap fun s => s.auras.map (s.who, ·)

/-- そのカードがフィールドに表側表示で存在し、効果が無効化されているか -/
def srcNegated (b : Board) (key : Nat × Nat × Nat) : Bool :=
  b.sources.any (·.key == key) && !b.effective.any (·.key == key)

/-- 魔法・罠ゾーンの i 番目のカードの効果が無効化されているか -/
def stNegated (b : Board) (w : PlayerId) (i : Nat) : Bool := b.srcNegated (stKey w i)

/-- モンスターの効果が無効化されているか -/
def monNegated (b : Board) (uid : Nat) : Bool := b.srcNegated (monKey uid)

/-- 永続効果の有効・無効の判定結果をモンスターに書き込む -/
def _root_.YGO.FieldMonster.commitAura (r : List AuraSrc) (m : FieldMonster) : FieldMonster :=
  match r.find? (·.key == monKey m.uid) with
  | some s => { m with since := s.since, negated := !s.on }
  | none => m

/-- 永続効果の有効・無効の判定結果を魔法・罠ゾーンのカードに書き込む -/
def _root_.YGO.SetCard.commitAura (r : List AuraSrc) (key : Nat × Nat × Nat) (c : SetCard) : SetCard :=
  match r.find? (·.key == key) with
  | some s => { c with since := s.since, negated := !s.on }
  | none => c

/-- 永続効果の有効・無効の判定結果をプレイヤーのカードに書き込む -/
def _root_.YGO.Player.commitAuras (p : Player) (w : PlayerId) (r : List AuraSrc) : Player :=
  { p with monsters := p.monsters.map (·.commitAura r),
           backrow := p.backrow.mapIdx fun i c => c.commitAura r (stKey w i) }

/-- 永続効果の有効・無効の判定結果を盤面に書き込む。1手進めるたびに行う。
有効・無効は前回の判定結果から順に変わっていくので（`settleOnce`）、盤面だけからは決まらない。 -/
def commitAuras (b : Board) : Board :=
  let r := settle b.sources b.clock
  { b with p1 := b.p1.commitAuras .one r.1, p2 := b.p2.commitAuras .two r.1, clock := r.2 }

/-- チェーン上の罠カードの効果が無効化されるか（フィールドの罠を無効にする効果が適用中か） -/
def trapsNegated (b : Board) : Bool :=
  b.auras.any (·.2 == .negateTraps)

/-- 罠カードを発動できないか -/
def trapsLocked (b : Board) : Bool :=
  b.auras.any (·.2 == .noTrapActivation)

/-- 永続効果による攻撃力の変化。`own` は永続効果のコントローラーがモンスターと同じか。 -/
def _root_.YGO.Aura.atkMod (a : Aura) (own : Bool) (c : MonsterCard) : Int :=
  match a with
  | .atkUpOwn r n =>
    if own && (match r with | none => true | some r => c.race == r) then n else 0
  | .oppAtkDownPerLevel n => if own then 0 else -((c.level?.getD 0 * n : Nat) : Int)
  | _ => 0

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
  let since := b.clock + 1
  let b := b.modify w fun p =>
    { p with monsters := p.monsters ++ [{ uid, card := c, pos, summonedTurn := turn, emz, overlays, since }] }
  { b with nextUid := uid + 1, clock := since, log := b.log ++ (ev.map (Happened.mk w c · uid)).toList }

/-- uid のモンスターの位置 -/
def findMonIdx (b : Board) (uid : Nat) : Option (PlayerId × Nat) :=
  match b.p1.monsters.findIdx? (·.uid == uid) with
  | some i => some (.one, i)
  | none => (b.p2.monsters.findIdx? (·.uid == uid)).map (.two, ·)

/-- i 番目のモンスターを置き換える -/
def setMonAt (b : Board) (w : PlayerId) (i : Nat) (m : FieldMonster) : Board :=
  b.modify w fun p => { p with monsters := p.monsters.set i m }

/-- uid のモンスターをフィールドから取り除く。そのモンスターの装備カードは墓地へ送られる。 -/
def detach (b : Board) (uid : Nat) : Option (Board × PlayerId × FieldMonster) := do
  let (w, i) ← b.findMonIdx uid
  let m ← (b.get w).monsters[i]?
  let b := b.modify w fun p => { p with monsters := p.monsters.eraseIdx i }
  let dropEquips (p : Player) : Player :=
    { p with backrow := p.backrow.filter (·.equipTo != some uid)
             grave := p.grave ++ (p.backrow.filter (·.equipTo == some uid)).map (·.card) }
  pure ((b.modify .one dropEquips).modify .two dropEquips, w, m)

/-- uid のモンスターを墓地へ送る（X素材も墓地へ）。
破壊された場合、そのモンスターと関係を持つ永続罠も破壊する。ただし、その時点（モンスターが離れた後）で
罠の効果が無効化されていれば何も起きない。 -/
def toGraveMon (b : Board) (uid : Nat) (cause : LeaveCause := .sent) : Board :=
  match b.detach uid with
  | none => b
  | some (b, w, m) =>
    let b := b.modify w fun p => { p with grave := p.grave ++ m.overlays ++ [.monster m.card] }
    let evs := (if cause == .battle then [Event.destroyedByBattle] else []) ++ [.sentToGraveFromField]
    let b := { b with log := b.log ++ evs.map (Happened.mk w m.card · uid) }
    if cause == .sent then b
    else
      -- 関係を持つ永続罠のうち、その時点で効果が無効化されていないものを（同時に）破壊する
      let doomed (v : PlayerId) : List Nat :=
        (List.range (b.get v).backrow.length).filter fun i =>
          ((b.get v).backrow[i]?.bind (·.bond)) == some uid && !b.stNegated v i
      let drop (b' : Board) (v : PlayerId) : Board :=
        b'.modify v fun p =>
          let r := removeIdxs p.backrow (doomed v)
          { p with backrow := r.1, grave := p.grave ++ r.2.map (·.card) }
      drop (drop b .one) .two

/-- モンスターを順に取り除き、取り除けたモンスターを集める（エクシーズ素材用） -/
def detachAllAux : Board × List FieldMonster → List FieldMonster → Board × List FieldMonster
  | acc, [] => acc
  | acc, m :: ms =>
    detachAllAux (match acc.1.detach m.uid with
      | some (b, _, x) => (b, acc.2 ++ [x])
      | none => acc) ms

def detachAll (b : Board) (ms : List FieldMonster) : Board × List FieldMonster := detachAllAux (b, []) ms

def destroyAllOf (b : Board) (w : PlayerId) : Board :=
  (b.get w).monsters.foldl (fun b m => b.toGraveMon m.uid .destroyed) b

/-- 魔法・罠ゾーンの i 番目のカードを破壊する。関係を持つモンスターがいれば、その時点で
効果が無効化されていない限りそのモンスターも破壊する。 -/
def destroyBackrow (b : Board) (w : PlayerId) (i : Nat) : Board :=
  match (b.get w).backrow[i]? with
  | none => b
  | some s =>
    let negated := b.stNegated w i
    let b := b.modify w fun p => { p with backrow := p.backrow.eraseIdx i, grave := p.grave ++ [s.card] }
    match s.bond with
    | some u => if negated then b else b.toGraveMon u .destroyed
    | none => b

/-- プレイヤー `ws` の魔法・罠ゾーンのカードを全て**同時に**破壊する。関係を持つモンスターを破壊するかは、
破壊される直前の盤面で効果が有効かどうかで判定する（12/02/01、07/10/29）。 -/
def destroyAllBackrow (b : Board) (ws : List PlayerId) : Board :=
  let bonded := ws.flatMap fun w =>
    let p := b.get w
    (List.range p.backrow.length).filterMap fun i =>
      if b.stNegated w i then none else p.backrow[i]?.bind (·.bond)
  let b := ws.foldl (fun b w =>
    b.modify w fun p => { p with backrow := [], grave := p.grave ++ p.backrow.map (·.card) }) b
  bonded.foldl (fun b u => b.toGraveMon u .destroyed) b

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
def reviveOk (b : Board) (l : ChainLink) : Option (PlayerId × Nat × MonsterCard) :=
  match l.graveTarget with
  | some (w, i, .monster m) =>
    if (b.get w).grave[i]? = some (.monster m) ∧ (l.eff = .revive true → w = l.owner) ∧
        (b.get l.owner).mainFree then some (w, i, m) else none
  | _ => none

/-- 融合素材の条件を満たすか。満たすなら融合モンスターを出すゾーンを返す。 -/
def fusionCheck (b : Board) (l : ChainLink) (fm : MonsterCard) : Option Bool := do
  let p := b.get l.owner
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
  p.slotAfter l.fieldMats false

/-- 融合召喚できるか。できるなら融合モンスターとエクストラデッキでの位置を返す。 -/
def fusionPlan (b : Board) (l : ChainLink) : Option (MonsterCard × Nat × Bool) :=
  match l.extra with
  | some (i, .monster fm) =>
    if (b.get l.owner).extra[i]? = some (.monster fm) then (fusionCheck b l fm).map (fm, i, ·) else none
  | _ => none

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
  | .destroyTarget => l.targets.foldl (fun b u => b.toGraveMon u .destroyed) b
  | .revive _ =>
    match reviveOk b l with
    | none => b
    | some (w, i, m) =>
      (b.modify w fun p => { p with grave := p.grave.eraseIdx i }).place self m .attack c.turn
        false (some .specialSummoned)
  | .fusionSummon =>
    match fusionPlan b l with
    | none => b
    | some (fm, i, _) =>
      let b := b.modify self fun p =>
        let r := removeIdxs p.hand (l.handMats.map (·.1))
        { p with hand := r.1, grave := p.grave ++ r.2 }
      let b := l.fieldMats.foldl (fun b u => b.toGraveMon u) b
      -- 素材が離れた後のゾーンの空きを確認してから出す
      match (b.get self).slotAfter [] false with
      | some emz =>
        (b.modify self fun p => { p with extra := p.extra.eraseIdx i }).place self fm .attack c.turn emz
          (some .specialSummoned)
      | none => b
  | .destroyAttacker =>
    match b.attack with
    | some bt => { b.toGraveMon bt.attacker .destroyed with attack := none }
    | none => b
  | .negateAttack => { b with attack := none }
  | .destroyOppSpellTraps => b.destroyAllBackrow [self.other]
  | .destroyAllSpellTraps => b.destroyAllBackrow [.one, .two]
  | .millOpp n =>
    b.modify self.other fun p => { p with deck := p.deck.drop n, grave := p.grave ++ p.deck.take n }
  | .recruit attr mx =>
    let p := b.get self
    let ok : Card → Bool
      | .monster m => m.attr == attr && m.atk ≤ mx
      | _ => false
    match p.deck.findIdx? ok with
    | some i =>
      match p.deck[i]? with
      | some (.monster m) =>
        if p.mainFree then
          (b.set self { p with deck := p.deck.eraseIdx i }).place self m .attack c.turn
            false (some .specialSummoned)
        else b
      | _ => b
    | none => b
  | .searchMaxDef d =>
    let p := b.get self
    let ok : Card → Bool
      | .monster m => m.dfs ≤ d
      | _ => false
    match p.deck.findIdx? ok with
    | some i =>
      match p.deck[i]? with
      | some cd => b.set self { p with deck := p.deck.eraseIdx i, hand := p.hand ++ [cd] }
      | none => b
    | none => b

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
  | .revive _ => unless (reviveOk b l).isSome do throw "蘇生できるモンスターがいない、またはゾーンに空きがない"
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

/-- 処理時に効果が無効化されているか。
* 罠カードの効果は、罠の効果が無効化されていれば無効
* モンスター効果は、そのモンスターがフィールドに表側表示で存在し、モンスターの効果が無効化されていれば無効。
  フィールドを離れたモンスター（コストでリリースした、墓地で発動した等）の効果は無効にならない。 -/
def Board.effectNegated (b : Board) (l : ChainLink) : Bool :=
  (!l.mon && l.card.isTrap && b.trapsNegated) ||
  l.mon &&
    match l.src.bind b.findMon with
    | some (_, m) => m.pos != .faceDownDefense && b.monNegated m.uid
    | none => false

/-- 1つのチェーンブロックを解決する。永続・装備カードはフィールドに表側で残る。 -/
def resolveLink (c : Ctx) (b : Board) (l : ChainLink) : Board :=
  let b0 := b
  let b := if b.effectNegated l then b else applyEffect c l b
  if l.mon then b else
  -- 効果で特殊召喚したモンスターの uid
  let summoned := if b0.nextUid < b.nextUid then some b0.nextUid else none
  let keep (eq bond : Option Nat) : Board :=
    let since := b.clock + 1
    { b.modify l.owner (fun p =>
        { p with backrow := p.backrow ++
            [{ card := l.card, setTurn := c.turn, faceUp := true, equipTo := eq, bond, since }] })
      with clock := since }
  match l.card with
  | .spell _ (.continuous _) => keep none none
  | .trap _ (.continuous ..) => keep none (if l.card.bonds then summoned else none)
  | .spell _ (.equip _) =>
    match l.targets with
    | [u] =>
      match b.findMon u with
      | some (_, m) => if m.pos = .faceDownDefense then toGrave b l else keep (some u) none
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
  | .trap .. =>
    if s.board.trapsLocked then throw "罠カードを発動できない（永続効果）"
    unless sc.setTurn < c.turn do throw "罠はセットしたターンには発動できない"
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
  let b := b.setMonAt who z { m with effectUsed := true }
  let b ← match cost with
    | .free => pure b
    | .tributeSelf => pure (b.toGraveMon m.uid)
    | .payLP n =>
      if n < (b.get who).lp then pure (b.modify who (·.damage n)) else throw "LP が足りない"
    | .detach n =>
      if n ≤ m.overlays.length then
        pure ((b.setMonAt who z { m with effectUsed := true, overlays := m.overlays.drop n }).modify who
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
  let b := tms.foldl (fun b t => b.toGraveMon t.uid) b
  let b := b.modify c.active fun p => { p with hand := p.hand.eraseIdx h }
  -- リリースしたモンスターが離れた後のゾーンの空きを確認する
  unless (b.get c.active).mainFree do throw "モンスターゾーンに空きがない"
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
  -- 素材が離れた後のゾーンの空きを確認してから出す
  let summon (b : Board) (overlays : List Card) : Except String Board :=
    match (b.get c.active).slotAfter [] em.isLink with
    | some emz =>
      pure ((b.modify c.active fun p => { p with extra := p.extra.eraseIdx ei }).place c.active em
        .attack c.turn emz (some .specialSummoned) overlays)
    | none => throw "モンスターゾーンに空きがない"
  match em.kind with
  | .xyz _ =>
    -- 素材は墓地へ送らず、X素材として重ねる（取り除けたモンスターだけを重ねる）
    let (b, got) := b.detachAll ms
    let b := b.modify c.active fun p => { p with grave := p.grave ++ got.flatMap (·.overlays) }
    summon b (got.map fun m => Card.monster m.card)
  | _ => summon (ms.foldl (fun b m => b.toGraveMon m.uid) b) []

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
          let b := if flipped then { b with clock := b.clock + 1 } else b
          let since := b.clock
          let d := if flipped then { d with pos := .faceUpDefense, since } else d
          let b := b.updMon opp tu fun x => if flipped then { x with pos := .faceUpDefense, since } else x
          let b := if flipped then { b with log := b.log ++ [⟨opp, d.card, .flipped, tu⟩] } else b
          let r := resolveBattle aAtk d.pos (b.atkOf opp d) d.card.dfs
          let b := (b.modify me (·.damage r.dmgToAttacker)).modify opp (·.damage r.dmgToDefender)
          let b := if r.attackerDestroyed then b.toGraveMon a.uid .battle else b
          if r.defenderDestroyed then b.toGraveMon tu .battle else b

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
  let since := b.clock + 1
  let b := b.updMon c.active m.uid fun x => { x with pos := .attack, posChanged := true, since }
  return { b with clock := since, log := b.log ++ [⟨c.active, m.card, .flipped, m.uid⟩] }

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
  else (act g.ctx g.cs a).map fun s =>
    checkResult (g.setCs (processTriggers g.ctx { s with board := s.board.commitAuras }))

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
theorem effectNegated_offField (b : Board) (l : ChainLink) (hm : l.mon = true)
    (h : l.src.bind b.findMon = none) : b.effectNegated l = false := by
  simp [Board.effectNegated, hm, h]

/-- **罠の効果が無効化されていれば、罠カードの効果は処理時に無効になる**（サイコ・ショッカー） -/
theorem effectNegated_trap (b : Board) (l : ChainLink) (hm : l.mon = false) (ht : l.card.isTrap = true)
    (hn : b.trapsNegated = true) : b.effectNegated l = true := by
  simp [Board.effectNegated, hm, ht, hn]

/-- **一方的に無効にする永続効果は、適用の順番に関係なく優先される**（王宮のお触れ → スキルドレイン） -/
theorem beats_one_way (t s : AuraSrc) (hts : t.negates s = true) (hst : s.negates t = false) :
    t.beats s = true := by
  simp [AuraSrc.beats, hts, hst]

/-- **互いに無効にし合う永続効果は、先に適用された方が優先される**（スキルドレイン ⇄ サイコ・ショッカー） -/
theorem beats_mutual (t s : AuraSrc) (hts : t.negates s = true) (hst : s.negates t = true) :
    t.beats s = true ↔ t.since ≤ s.since := by
  simp [AuraSrc.beats, hts, hst]

/-- 互いに無効にし合うとき、両方が相手を無効にすることはない（適用の時刻が異なれば） -/
theorem beats_not_both (t s : AuraSrc) (hne : t.since ≠ s.since) :
    ¬ (t.beats s = true ∧ s.beats t = true) := by
  intro ⟨h1, h2⟩
  simp only [AuraSrc.beats, Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff] at h1 h2
  rcases h1 with ⟨h1a, h1b | h1b⟩ <;> rcases h2 with ⟨h2a, h2b | h2b⟩ <;> simp_all <;> omega

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

/-- 永続効果：お互いに罠カードを発動できず、フィールドの罠カードの効果は無効化される -/
def jinzo : MonsterCard :=
  { name := "人造人間－サイコ・ショッカー", level := 6, atk := 2400, dfs := 1500, attr := .dark,
    race := .machine, effects := [.continuous .noTrapActivation, .continuous .negateTraps] }

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
def harpieFeather : Card := .spell "ハーピィの羽根帚" (.normal .destroyOppSpellTraps)
def heavyStorm : Card := .spell "大嵐" (.normal .destroyAllSpellTraps)

-- 罠
def justDesserts : Card := .trap "仕込みマシンガン" (.normal (.burnPerOppMonster 500))
def darkBribe    : Card := .trap "魔宮の賄賂" (.counter (.negate 1))
def sakuretsu    : Card := .trap "炸裂装甲" (.normal .destroyAttacker)
def gravityBind  : Card := .trap "グラヴィティ・バインド－超重力の網－" (.continuous [.noAttackLevelGE 4])
def skillDrain   : Card := .trap "スキルドレイン" (.continuous [.negateMonsterEffects] (.payLP 1000))
/-- このカード以外のフィールドの罠カードの効果は無効化される -/
def royalDecree  : Card := .trap "王宮のお触れ" (.continuous [.negateTraps])
/-- 自分の墓地のモンスター1体を攻撃表示で特殊召喚。このカードが離れた時にそのモンスターは破壊され、
そのモンスターが破壊された時にこのカードは破壊される。 -/
def callOfHaunted : Card := .trap "リビングデッドの呼び声" (.continuous [] .free (.revive true) true)

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

/-- info: Except.ok (6, 6200, 5200, some (YGO.Outcome.win (YGO.PlayerId.one))) -/
#guard_msgs in
#eval final.map (fun g => (g.turn, g.board.p1.lp, g.board.p2.lp, g.result))

set_option maxRecDepth 2000 in
/-- この対戦は P1 のデッキ切れ勝ちで終わる（カーネルで検証） -/
example : (final.toOption.bind (·.result)) = some (.win .one) := by decide

-- 反則の例
/-- info: Except.ok (2, YGO.PlayerId.two, 6) -/
#guard_msgs in
#eval (play (Game.init deck1 deck2) [np, np, np, np]).map (fun g => (g.turn, g.active, g.board.p2.hand.length))
/-- info: Except.error "通常召喚（セット）は1ターンに1度まで" -/
#guard_msgs in
#eval (play (Game.init deck1 deck2) [np, np, .normalSummon 0 [], .normalSummon 0 []]).map (·.turn)
/-- info: Except.error "攻撃はバトルフェイズにしか行えない" -/
#guard_msgs in
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

/-- info: Except.ok (8000, 7200, 1, 0) -/
#guard_msgs in
#eval chainEnd.map (fun g => (g.board.p1.lp, g.board.p2.lp, g.board.p2.hand.length, g.chain.length))

/-- 仕込みマシンガンは無効にされ、P1 は無傷。P2 は 800 ダメージを受けて1枚ドロー -/
example : chainEnd.toOption.map (fun g => (g.board.p1.lp, g.board.p2.lp, g.board.p2.hand.length))
    = some (8000, 7200, 1) := by decide

-- 優先権：P1 がパスするまで P2 は発動できない
/-- info: Except.error "優先権を持っていない" -/
#guard_msgs in
#eval (play chainStart [.activateSet .two 0]).map (fun _ => ())
/-- info: Except.ok 7500 -/
#guard_msgs in
#eval (play chainStart [.pass, .activateSet .two 0, .pass, .pass]).map (fun g => g.board.p1.lp)
-- 反則の例：チェーン中のフェイズ移行、スペルスピード1のチェーン、カウンター罠への通常罠
/-- info: Except.error "チェーンや攻撃の処理中、または優先権がないときはフェイズを進められない" -/
#guard_msgs in
#eval (play chainStart [.activateSpell 0, .nextPhase]).map (fun _ => ())
/-- info: Except.error "スペルスピード1はチェーンに組めない" -/
#guard_msgs in
#eval (play { chainStart with board := (chainStart.board.modify .one
              (fun p => { p with hand := [ookazi, hinotama] })) }
        [.activateSpell 0, .pass, .activateSpell 0]).map (fun _ => ())
/-- info: Except.error "スペルスピード3にはスペルスピード3以上でしかチェーンできない" -/
#guard_msgs in
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

/-- info: Except.ok (["ブラック・デーモンズ・ドラゴン"], ["真紅眼の黒竜", "デーモンの召喚", "融合"]) -/
#guard_msgs in
#eval fusionEnd.map (fun g => (names g.board.p1.monsters, g.board.p1.grave.map (·.name)))

example : fusionEnd.toOption.map (fun g => (names g.board.p1.monsters, g.board.p1.grave.length,
    g.board.p1.extra.length)) = some (["ブラック・デーモンズ・ドラゴン"], 3, 0) := by decide

-- 素材が足りなければ発動できない
/-- info: Except.error "融合召喚の条件を満たしていない" -/
#guard_msgs in
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

/-- info: Except.ok ["エルフの剣士", "大地の騎士ガイアナイト"] -/
#guard_msgs in
#eval (play synchroStart [.extraSummon 0 [0, 1]]).map (fun g => names g.board.p1.monsters)

example : (play synchroStart [.extraSummon 0 [0, 1]]).toOption.map (fun g => names g.board.p1.monsters)
    = some ["エルフの剣士", "大地の騎士ガイアナイト"] := by decide

-- レベルの合計が合わない（3 + 4 = 7）
/-- info: Except.error "大地の騎士ガイアナイトの召喚条件を満たしていない" -/
#guard_msgs in
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

/-- info: Except.ok (["No.39 希望皇ホープ"], [2]) -/
#guard_msgs in
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

/-- info: Except.ok (8000, ["No.39 希望皇ホープ"], [1], false) -/
#guard_msgs in
#eval hopeEnd.map (fun g => (g.board.p1.lp, names g.board.p1.monsters,
  g.board.p1.monsters.map (·.overlays.length), g.board.attack.isSome))

example : hopeEnd.toOption.map (fun g => (g.board.p1.lp, g.board.p1.monsters.map (·.overlays.length)))
    = some (8000, [1]) := by decide

-- 炸裂装甲で攻撃モンスターを破壊する
/-- info: Except.ok ([], ["青眼の白龍"]) -/
#guard_msgs in
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

/-- info: Except.ok [("岩石の巨兵", false), ("ホーリー・エルフ", false), ("プロキシー・ドラゴン", true)] -/
#guard_msgs in
#eval (play linkStart [.extraSummon 0 [0, 1]]).map
  (fun g => g.board.p1.monsters.map (fun m => (m.card.name, m.emz)))
/-- info: Except.error "モンスターゾーンに空きがない" -/
#guard_msgs in
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

/-- info: Except.ok (6400, ["黒き森のウィッチ"], 2) -/
#guard_msgs in
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

/-- info: Except.ok (0, 1, 5) -/
#guard_msgs in
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

/-- info: Except.ok (0, 0, ["クリボー"]) -/
#guard_msgs in
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

/-- info: Except.ok (["聖鳥クレイン"], ["クリボー"]) -/
#guard_msgs in
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
/-- info: Except.ok [1200, 2400] -/
#guard_msgs in
#eval auraEnd.map (fun g => g.board.p1.monsters.map (g.board.atkOf .one ·))

example : auraEnd.toOption.map (fun g => g.board.p1.monsters.map (g.board.atkOf .one ·))
    = some [1200, 2400] := by decide

-- 装備モンスターがフィールドを離れると装備カードも墓地へ送られる
/-- info: Except.ok (0, ["デーモンの斧", "エルフの剣士"]) -/
#guard_msgs in
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

/-- info: Except.error "永続効果により攻撃宣言できない" -/
#guard_msgs in
#eval (play gravityStart [.attack 0 none]).map (fun _ => ())
/-- info: Except.ok 5500 -/
#guard_msgs in
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

/-- info: Except.ok ([], ["クリボー"]) -/
#guard_msgs in
#eval drainExiledEnd.map (fun g => (names g.board.p2.monsters, g.board.p2.hand.map (·.name)))

example : drainExiledEnd.toOption.map (fun g => (names g.board.p2.monsters, g.board.p2.hand.map (·.name)))
    = some ([], ["クリボー"]) := by decide

/-- ホープはフィールドで効果を処理するので無効になる（発動はでき、X素材は取り除かれる）。
攻撃は続き、ホープは戦闘で破壊される。 -/
def drainHopeEnd : Except String Game :=
  play (withDrain hopeDefense)
    ([.attack 0 (some 0), .pass, .activateMonster .one 0, .pass, .pass] ++ [.pass, .pass])

/-- info: Except.ok (7500, [], 3) -/
#guard_msgs in
#eval drainHopeEnd.map (fun g => (g.board.p1.lp, names g.board.p1.monsters, g.board.p1.grave.length))

example : drainHopeEnd.toOption.map (fun g => (g.board.p1.lp, names g.board.p1.monsters))
    = some (7500, []) := by decide

-- 永続効果も無効になる：コマンド・ナイトの攻撃力アップが消える（強者の苦痛の -400 のみ）
/-- info: [800, 1000] -/
#guard_msgs in
#eval (withDrain auraStart).board.p1.monsters.map ((withDrain auraStart).board.atkOf .one ·)

/-- LP がちょうど 1000 のときはスキルドレインを発動できない（LP が 0 以下になるようには払えない） -/
def drainCostStart (lp : Nat) : Game where
  board := { p1 := { deck := [] },
             p2 := { deck := [], lp, backrow := [{ card := skillDrain, setTurn := 2 }] } }
  turn := 3
  active := .one
  phase := .main1

/-- info: Except.error "LP が足りないため発動できない" -/
#guard_msgs in
#eval (play (drainCostStart 1000) [.pass, .activateSet .two 0]).map (fun _ => ())
/-- info: Except.ok 1 -/
#guard_msgs in
#eval (play (drainCostStart 1001) (.pass :: resolve (.activateSet .two 0))).map (fun g => g.board.p2.lp)

example : (play (drainCostStart 1000) [.pass, .activateSet .two 0]).toOption.isNone := by decide

-- 戦闘で破壊され墓地へ送られた《キラー・トマト》の効果は墓地で処理されるので無効にならない
/-- info: Except.ok ["黒き森のウィッチ"] -/
#guard_msgs in
#eval (play (withDrain tomatoStart) (resolve (.attack 0 (some 0)) ++ [.pass, .pass])).map
  (fun g => names g.board.p1.monsters)

/-! ### サイコ・ショッカーとリビングデッドの呼び声
永続効果の有効・無効は、前回の判定結果とその時点の盤面から計算する。 -/

/-- P1 の墓地にサイコ・ショッカーとエルフの剣士、呼び声をセット済み。P2 の手札には羽根帚とサンダー・ボルト -/
def cothStart : Game where
  board := { p1 := { deck := [], hand := [.monster summonedSkull],
                     grave := [.monster jinzo, .monster celticGuardian],
                     backrow := [{ card := callOfHaunted, setTurn := 2 }] },
             p2 := { deck := [.monster kuriboh], hand := [harpieFeather, raigeki],
                     backrow := [{ card := sakuretsu, setTurn := 2 }] } }
  turn := 3
  active := .one
  phase := .main1

/-- 呼び声で墓地の target 番目（0 = ショッカー、1 = エルフの剣士）を蘇生する -/
def revive (target : Nat) : List Action := resolve (.activateSet .one 0 { grave := some (.one, target) })

/-- P1 のターンを終えて P2 のメインフェイズ1へ -/
def toP2Main : List Action := [np, np, np, np, np, np]

/-- info: Except.ok (["人造人間－サイコ・ショッカー"], [some 0], true) -/
#guard_msgs in
#eval (play cothStart (revive 0)).map
  (fun g => (names g.board.p1.monsters, g.board.p1.backrow.map (·.bond), g.board.trapsNegated))

-- ショッカーがいる間は、お互いに罠カードを発動できない
/-- info: Except.error "罠カードを発動できない（永続効果）" -/
#guard_msgs in
#eval (play cothStart (revive 0 ++ [.pass, .activateSet .two 0])).map (fun _ => ())

/-- 呼び声が破壊されても、その時点で呼び声の効果は無効なので、ショッカーは破壊されない -/
def cothFeather : Except String Game :=
  play cothStart (revive 0 ++ toP2Main ++ resolve (.activateSpell 0))

/-- info: Except.ok (["人造人間－サイコ・ショッカー"], 0, ["エルフの剣士", "リビングデッドの呼び声"]) -/
#guard_msgs in
#eval cothFeather.map (fun g => (names g.board.p1.monsters, g.board.p1.backrow.length, g.board.p1.grave.map (·.name)))

example : cothFeather.toOption.map (fun g => (names g.board.p1.monsters, g.board.p1.backrow.length))
    = some (["人造人間－サイコ・ショッカー"], 0) := by decide

/-- ショッカーが破壊されると、直後に罠の無効化が消えて呼び声の効果が有効になり、呼び声も破壊される（07/04/28） -/
def cothRaigeki : Except String Game :=
  play cothStart (revive 0 ++ toP2Main ++ resolve (.activateSpell 1))

/-- info: Except.ok ([], 0, ["エルフの剣士", "人造人間－サイコ・ショッカー", "リビングデッドの呼び声"]) -/
#guard_msgs in
#eval cothRaigeki.map (fun g => (names g.board.p1.monsters, g.board.p1.backrow.length, g.board.p1.grave.map (·.name)))

example : cothRaigeki.toOption.map (fun g => (names g.board.p1.monsters, g.board.p1.backrow.length))
    = some ([], 0) := by decide

-- 比較：ショッカー以外を蘇生した場合、呼び声が破壊されるとそのモンスターも破壊される
/-- info: Except.ok ([], ["人造人間－サイコ・ショッカー", "リビングデッドの呼び声", "エルフの剣士"]) -/
#guard_msgs in
#eval (play cothStart (revive 1 ++ toP2Main ++ resolve (.activateSpell 0))).map
  (fun g => (names g.board.p1.monsters, g.board.p1.grave.map (·.name)))

-- 比較：リリースは破壊ではないので、蘇生したモンスターをリリースしても呼び声は残る
/-- info: Except.ok (["デーモンの召喚"], 1) -/
#guard_msgs in
#eval (play cothStart (revive 1 ++ [.normalSummon 0 [0]])).map (fun g => (names g.board.p1.monsters, g.board.p1.backrow.length))

-- スキルドレインが適用中なら、ショッカーの効果は無効なので罠は発動でき、効果も無効にならない
/-- info: Except.ok (false, false) -/
#guard_msgs in
#eval (play (withDrain cothStart) (revive 0)).map (fun g => (g.board.trapsLocked, g.board.trapsNegated))

/-- スキルドレインと呼び声が同時に破壊される場合、破壊される直前はスキルドレインでショッカーの効果が
無効なので呼び声の効果は有効であり、ショッカーは破壊される（12/02/01） -/
def drainCothEnd : Except String Game :=
  let start := { cothStart with board := cothStart.board.modify .one fun p =>
    { p with backrow := { card := skillDrain, setTurn := 1, faceUp := true } :: p.backrow } }
  play start (resolve (.activateSet .one 1 { grave := some (.one, 0) }) ++ toP2Main ++ resolve (.activateSpell 0))

/-- info: Except.ok ([], ["エルフの剣士", "スキルドレイン", "リビングデッドの呼び声", "人造人間－サイコ・ショッカー"]) -/
#guard_msgs in
#eval drainCothEnd.map (fun g => (names g.board.p1.monsters, g.board.p1.grave.map (·.name)))

example : drainCothEnd.toOption.map (fun g => names g.board.p1.monsters) = some [] := by decide

/-! ### 王宮のお触れとリビングデッドの呼び声 -/

/-- P1：呼び声をセット、墓地にエルフの剣士、手札に羽根帚と大嵐。P2：お触れをセット、手札に羽根帚 -/
def decreeStart : Game where
  board := { p1 := { deck := [], hand := [harpieFeather, heavyStorm], grave := [.monster celticGuardian],
                     backrow := [{ card := callOfHaunted, setTurn := 2 }] },
             p2 := { deck := [.monster kuriboh], hand := [harpieFeather],
                     backrow := [{ card := royalDecree, setTurn := 2 }] } }
  turn := 3
  active := .one
  phase := .main1

def callCoth : Action := .activateSet .one 0 { grave := some (.one, 0) }

/-- 呼び声の発動にお触れをチェーンされると、特殊召喚は無効になり呼び声だけが残る。
その後でお触れを除去しても、改めて特殊召喚はされない -/
def decreeChain : Except String Game :=
  play decreeStart ([callCoth, .activateSet .two 0, .pass, .pass] ++ resolve (.activateSpell 0))

/-- info: Except.ok ([], ["リビングデッドの呼び声"], 0) -/
#guard_msgs in
#eval decreeChain.map (fun g => (names g.board.p1.monsters, g.board.p1.backrow.map (·.card.name),
  g.board.p2.backrow.length))

example : decreeChain.toOption.map (fun g => (names g.board.p1.monsters, g.board.p1.backrow.length))
    = some ([], 1) := by decide

/-- 蘇生後にお触れを発動され、次にお触れを破壊した後で呼び声が破壊されると、モンスターも破壊される。
途中で無効化されていても、破壊される時点で有効なら関係は適用される（07/03/28） -/
def decreeLater : Except String Game :=
  play decreeStart (resolve callCoth ++ [.pass] ++ resolve (.activateSet .two 0) ++
    resolve (.activateSpell 0) ++ toP2Main ++ resolve (.activateSpell 0))

/-- info: Except.ok ([], ["ハーピィの羽根帚", "リビングデッドの呼び声", "エルフの剣士"]) -/
#guard_msgs in
#eval decreeLater.map (fun g => (names g.board.p1.monsters, g.board.p1.grave.map (·.name)))

example : decreeLater.toOption.map (fun g => names g.board.p1.monsters) = some [] := by decide

-- 比較：お触れが残っていれば、呼び声が破壊されてもモンスターは破壊されない
/-- info: Except.ok ["エルフの剣士"] -/
#guard_msgs in
#eval (play decreeStart (resolve callCoth ++ [.pass] ++ resolve (.activateSet .two 0) ++
    toP2Main ++ resolve (.activateSpell 0))).map (fun g => names g.board.p1.monsters)

/-- お触れと呼び声が大嵐で同時に破壊される場合、モンスターは破壊されない（07/10/29） -/
def decreeStorm : Except String Game :=
  play decreeStart (resolve callCoth ++ [.pass] ++ resolve (.activateSet .two 0) ++ resolve (.activateSpell 1))

/-- info: Except.ok (["エルフの剣士"], 0, 0) -/
#guard_msgs in
#eval decreeStorm.map (fun g => (names g.board.p1.monsters, g.board.p1.backrow.length, g.board.p2.backrow.length))

example : decreeStorm.toOption.map (fun g => names g.board.p1.monsters) = some ["エルフの剣士"] := by decide

/-! ### 永続効果の適用順 -/

/-- コマンド・ナイトとスキルドレイン（ナイトの効果は無効）。P2 はお触れをセット、P1 は手札にスキルドレイン -/
def orderStart : Game where
  board := { p1 := { deck := [], hand := [],
                     monsters := [fm 0 commandKnight],
                     backrow := [{ card := skillDrain, setTurn := 1, faceUp := true, since := 1 }] },
             p2 := { deck := [], backrow := [{ card := royalDecree, setTurn := 2 }] },
             nextUid := 1, clock := 1 }
  turn := 3
  active := .one
  phase := .main1

def knightAtk (g : Game) : List Nat := g.board.p1.monsters.map (g.board.atkOf .one ·)

-- 適用中のスキルドレインでナイトの効果は無効（攻撃力 1200）
/-- info: [1200] -/
#guard_msgs in
#eval knightAtk orderStart

-- 後からお触れが適用されるとスキルドレインが無効になり、ナイトの効果が有効に戻る（攻撃力 1600）
/-- info: Except.ok [1600] -/
#guard_msgs in
#eval (play orderStart ([.pass] ++ resolve (.activateSet .two 0))).map knightAtk

example : (play orderStart ([.pass] ++ resolve (.activateSet .two 0))).toOption.map knightAtk
    = some [1600] := by decide

/-- 先にお触れが適用されていれば、後から発動したスキルドレインは無効（一方的に無効にするので順番によらない） -/
def decreeFirst : Game :=
  { orderStart with board := { orderStart.board with
      p1 := { orderStart.board.p1 with backrow := [{ card := skillDrain, setTurn := 1 }] },
      p2 := { orderStart.board.p2 with backrow := [{ card := royalDecree, setTurn := 2, faceUp := true, since := 1 }] } } }

/-- info: Except.ok ([1600], ["スキルドレイン"], 7000) -/
#guard_msgs in
#eval (play decreeFirst (resolve (.activateSet .one 0))).map
  (fun g => (knightAtk g, g.board.p1.backrow.map (·.card.name), g.board.p1.lp))

/-! ### スキルドレイン・サイコ・ショッカー・王宮のお触れの3すくみ
お触れはスキルドレインを、スキルドレインはショッカーを（先に適用されていれば）、ショッカーはお触れを無効にする。
有効・無効は1つずつ順に変わり、有効に戻ったカードはその時点で新たに適用されたものとして扱う。 -/

/-- P1：スキルドレイン（先に適用）とショッカー。P2：お触れをセット -/
def triStart : Game where
  board := { p1 := { deck := [], monsters := [{ fm 0 jinzo with since := 2 }],
                     backrow := [{ card := skillDrain, setTurn := 1, faceUp := true, since := 1 }] },
             p2 := { deck := [], backrow := [{ card := royalDecree, setTurn := 2 }] },
             nextUid := 1, clock := 2 }
  turn := 3
  active := .one
  phase := .main1

/-- (スキルドレイン, ショッカー, お触れ) の効果が無効化されているか -/
def triNegated (g : Game) : List Bool :=
  [g.board.stNegated .one 0, g.board.monNegated 0, g.board.stNegated .two 0]

-- スキルドレインでショッカーの効果は無効なので、罠を発動できる
/-- info: [false, true, false] -/
#guard_msgs in
#eval triNegated triStart

/-- お触れが適用されると
1. スキルドレインが無効になる
2. ショッカーの効果が有効に戻り（この時点で適用）、お触れを無効にする
3. お触れが無効になってスキルドレインが有効に戻るが、先に適用されたショッカーに無効にされる

ショッカーの効果だけが有効になる（マスターデュエルで確認） -/
def triDecree : Except String Game := play triStart ([.pass] ++ resolve (.activateSet .two 0))

/-- info: Except.ok ([true, false, true], true, true) -/
#guard_msgs in
#eval triDecree.map (fun g => (triNegated g, g.board.trapsLocked, g.board.trapsNegated))

example : triDecree.toOption.map triNegated = some [true, false, true] := by decide

end Demo

end YGO
