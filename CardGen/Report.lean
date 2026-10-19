import CardGen.Timed
import CardGen.Pool
import CardGen.Turn

/-!
# 検査ツールの報告

中間表現の JSON を受け取り、次をまとめて返す。

- `errors`：形式の誤り（あれば★と無効の検査は行わない）
- `claims`：ルールから導いた★。どれも `CardGen.derived_valid` で証明済み
- `negation`：無効の関係の検査。循環がなければ `CardGen.negation_settles` で証明済み。
  循環があれば、まとまりごとに小さな盤面を総当たりで調べた結果（`CardGen.exploreGroup`）。
  分類は OCG の手順（適用の時刻つき、`Timed.lean`）による

命題の状態は `proved`（証明済み）、`counterexample`（反例あり）、`choice`（プレイヤーの選択）、
`unknown`（未確定）のどれか。
-/

namespace CardGen
open Lean

structure ClaimOut where
  text : String
  grounds : List String
  status : String
  «theorem» : String
deriving ToJson, FromJson, Repr

structure SideCard where
  card : String
  /-- `"self"`（自分）または `"opp"`（相手） -/
  side : String
deriving ToJson, FromJson, Repr

/-- 循環のまとまり1つの総当たりの結果 -/
structure GroupOut where
  cards : List String
  status : String
  message : String
  /-- 一番悪い結果になった盤面 -/
  board : List SideCard
  /-- その盤面のターンプレイヤー（`"self"`・`"opp"`。盤面がなければ `none`） -/
  turn : Option String
  /-- 調べた盤面の数 -/
  boards : Nat
  /-- 順番を自由にした判定（反転の手続き）での結果 -/
  detail : String
deriving ToJson, FromJson, Repr

structure NegOut where
  status : String
  message : String
  edges : List (List String)
  groups : List GroupOut
  «theorem» : Option String
deriving ToJson, FromJson, Repr

structure Report where
  /-- 報告の形式の版 -/
  version : Nat
  ok : Bool
  errors : List String
  claims : List ClaimOut
  negation : Option NegOut
deriving ToJson, FromJson, Repr

def sideCards (b : List (String × Bool)) : List SideCard :=
  b.map fun (c, mine) => ⟨c, if mine then "self" else "opp"⟩

def flipDetail : Verdict → String
  | .ok => "順番を自由にした判定でも、調べた盤面ではどう選んでも止まり、結果は1通りです"
  | .someLoop => "順番を自由にした判定では、選び方によって回り続ける盤面があります"
  | .multiStable => "順番を自由にした判定では、安定な状態が複数ある盤面があります"
  | .cannotHalt => "順番を自由にした判定では、どう選んでも止まらない状態がある盤面があります"
  | .noStable => "順番を自由にした判定では、どの状態も安定しない盤面があります"

def groupOut (g : GroupResult) : GroupOut :=
  if g.boards == 0 then
    ⟨g.cards, "unknown", s!"カードが{exploreLimit}枚を超えるため、総当たりで調べていません", [], none, 0, ""⟩
  else
    let turn := if g.timedTurn then "自分のターン" else "相手のターン"
    let (status, message) : String × String := match g.timed with
      | .unique | .byHistory => ("unknown",
          s!"各カードを1人{maxCopies}枚まで、合計{timedLimit}枚まで、ゾーンの容量を守って置いた盤面では、" ++
          "OCG の手順（適用の時刻）で、どちらのターンでも、どう選んでも判定は止まり、結果は適用された順番だけで決まります" ++
          (if g.certified then "（証明書を検査済み：CardGen.TSys.allEnd_of_certOK）" else "") ++
          "。それより大きい盤面は調べていません")
      | .choiceResult => ("choice", s!"この盤面の{turn}では、有効に戻すカードの選び方によって結果が変わります")
      | .someLoop => ("choice", s!"この盤面の{turn}では、選び方によって判定が回り続けます（止まる選び方はあります）")
      | .cannotHalt => ("counterexample", s!"この盤面の{turn}では、どう選んでも判定が止まらない状態があります")
      | .noStable => ("counterexample", s!"この盤面では、{turn}にどの状態から始めても判定が止まりません")
    let bad := g.timed.severity ≥ TVerdict.choiceResult.severity
    ⟨g.cards, status, message, if bad then sideCards g.timedBoard else [],
      if bad then some (if g.timedTurn then "self" else "opp") else none, g.boards,
      flipDetail g.verdict ++ (if g.board.isEmpty then "" else
        s!"（盤面：{"、".intercalate (g.board.map fun (c, m) => (if m then "自分：" else "相手：") ++ c)}）")⟩

def statusSeverity : String → Nat
  | "counterexample" => 3
  | "unknown" => 2
  | "choice" => 1
  | _ => 0

def negOut (r : Rules) (cards : List Card) : NegOut :=
  let edges := (negEdges cards).map fun (a, b) => [a, b]
  match checkNegation cards with
  | .none => ⟨"proved", "無効にする効果を持つカードはありません", edges, [], none⟩
  | .proved =>
    ⟨"proved", "無効にしうる関係に循環はありません。どの盤面でも、無効の判定はどの順番で進めても必ず止まり、結果は1通りです",
      edges, [], some "CardGen.negation_settles"⟩
  | .cyclic gs =>
    let groups := gs.map fun names =>
      groupOut (exploreGroup r (names.filterMap fun nm => cards.find? (·.name == nm)))
    let worst := groups.foldl (fun w g => if statusSeverity g.status > statusSeverity w then g.status else w) "choice"
    ⟨worst, "無効にしうる関係に循環があります。循環のまとまりごとに、小さな盤面を総当たりで調べました",
      edges, groups, none⟩

def Effect.isBoost : Effect → Bool
  | .boost .. => true
  | .toughen .. => true
  | _ => false

/-- 攻撃力・守備力が1通りに決まるか（攻撃力・守備力の変化と無効の関係の衝突）。変化を持つカードがなければ `none` -/
def attackClaim (cards : List Card) : Option ClaimOut :=
  if !cards.any (·.effects.any Effect.isBoost) then none else
  match checkNegation cards with
  | .cyclic _ =>
    let n := cards.length
    let reach := (List.range n).map (reachFrom cards)
    let onCycle := (List.range n).filter fun i => (reach.getD i []).contains i
    -- 循環のカードから無効の矢印をたどって届く（＝有効かどうかが循環に左右されうる）攻撃力の変化のカード
    let hit := (List.range n).filter fun j =>
      (cards[j]?.any (·.effects.any Effect.isBoost)) && onCycle.any fun i => (reach.getD i []).contains j
    let names := hit.filterMap fun j => cards[j]?.map (·.name)
    if names.isEmpty then
      some ⟨"攻撃力・守備力の変化を持つカードは、無効の循環の影響を受けません",
        ["無効にしうる関係の循環から、攻撃力の変化を持つカードへは矢印がたどれない"], "unknown", ""⟩
    else
      some ⟨s!"攻撃力・守備力の変化（{"、".intercalate names}）が効くかどうかは無効の判定の進み方で変わりうるので、" ++
          "攻撃力・守備力が1通りに決まらない盤面があります",
        ["無効にしうる関係の循環から、これらのカードは無効にされうる"], "choice", ""⟩
  | _ => some ⟨"攻撃力・守備力は、どの盤面でも1通りに決まります",
      ["無効にしうる関係に循環がないので、どのカードの効果が有効かは1通りに決まる（メタ定理1）",
       "攻撃力・守備力の変化は足し算なので、適用する順番によらない"], "proved", "CardGen.negation_settles"⟩

/-- ターンについての★（`Turn.lean`）。どれも証明済み -/
def turnClaims (r : Rules) (cards : List Card) : List ClaimOut :=
  let fighters := "・".intercalate r.fighters
  [⟨"優先権を持つプレイヤーだけが動けます（パスすると相手に移り、両者が続けてパスしたらスタックの一番上を解決するかブロックに進む）",
    ["公理：優先権を持つプレイヤーだけが動ける", "動いた本人が優先権を持ち続け、パスすると相手に移る"],
    "proved", "CardGen.Match.step?_prio"⟩,
   ⟨"ターンのある対戦でも、ここに挙げた★と盤面の制約はそのまま成り立ちます",
    ["ターンのある対戦の盤面は、どれもターンのない（いつでも何度でも動ける）モデルで到達できる盤面"],
    "proved", "CardGen.TReachable.of_reachable"⟩] ++
  (if r.fighters.isEmpty || r.summonsPerTurn == 0 then [] else
    [⟨s!"戦闘できるカード（{fighters}）を置けるのは、1ターンに {r.summonsPerTurn} 枚まで",
      [s!"ルール：1ターンの召喚の上限は {r.summonsPerTurn}"], "proved", "CardGen.TReachable.summons_le"⟩]) ++
  (if r.fighters.isEmpty then [] else
    [⟨"戦闘できるカードの攻撃は、1ターンに1枚1回まで",
      ["攻撃したカードの記録は、いつもターンプレイヤーのフィールドのカードの一部（同じカードの枚数も含めて）"],
      "proved", "CardGen.TReachable.attacked_bagLe"⟩]) ++
  r.placeLimits.map (fun l =>
    ⟨s!"「{"・".intercalate l.types}」を置けるのは、1ターンに {l.count} 枚まで",
      [s!"ルール：「{"・".intercalate l.types}」を1ターンに置ける枚数の上限は {l.count}"], "proved",
      "CardGen.TReachable.placed_le"⟩) ++
  (if r.attackTaps then
    [⟨"タップしているカードは、持ち主の次のターンが来るまで、攻撃にもマナにも使えない",
      ["ルール：攻撃するとタップする", "タップしたカードの記録は、いつもフィールドのカードの一部（同じカードの枚数も含めて）"],
      "proved", "CardGen.TReachable.fits"⟩] else []) ++
  (if r.blocking && !r.fighters.isEmpty then
    [⟨"ブロックは、1ターンに1枚1回まで（1枚の攻撃を何枚でブロックしてもよい）",
      ["ルール：攻撃されたプレイヤーがブロックするカードを選ぶ（MTG 式の戦闘）",
       "ブロックしたカードの記録は、いつも相手のフィールドのカードの一部（同じカードの枚数も含めて）"],
      "proved", "CardGen.TReachable.fits"⟩] else []) ++
  [⟨(if r.life > 0 then "ライフが 0 になるか、" else "") ++ "ターンの最初に引く枚数が足りなければ対戦は終わり、それ以上どの動きもできない",
    ["対戦が終わったかは、ライフとデッキ切れの記録で決まる"], "proved", "CardGen.Match.step?_over"⟩] ++
  (if r.blocking || cards.any (fun c => c.effects.any fun
      | .activated as => as.any fun | .strike .. | .pump .. => true | _ => false
      | _ => false) then
    [⟨"受けたダメージと、ターンの終わりまでの攻撃力・守備力の変化は、次のターンに残らない",
      ["ターン終了で、どのカードのダメージと一時的な変化も 0 に戻す"], "proved", "CardGen.Match.endTurn_clean"⟩] else []) ++
  (if r.stack then
    [⟨"スタックに積まれたカードは、いつも置いたプレイヤーのスタックのゾーンにある（打ち消されたり手札に戻されたりしたら、スタックからも消える）",
      ["スタックの記録は、動きのたびにフィールドにあるものだけに絞る"], "proved", "CardGen.TReachable.stack_fits"⟩] else []) ++
  (if cards.any (fun c => c.cost > 0 || !c.colorCost.isEmpty) then
    [⟨"1ターンに払うマナは、そのターンにタップして出したマナを超えない（マナはターンの終わりに消える）",
      ["カードを置くには、持っているマナからコストの分を払う", "持っているマナと払ったマナの合計は、そのターンにタップで出したマナに等しい"],
      "proved", "CardGen.TReachable.spent_le"⟩] else [])

def report (input : String) : Report :=
  let fail (es : List String) : Report := ⟨1, false, es, [], none⟩
  match Json.parse input with
  | .error e => fail [s!"JSON として読めません：{e}"]
  | .ok j =>
    match (fromJson? j : Except String Game) with
    | .error e => fail [s!"中間表現として読めません：{e}"]
    | .ok g =>
      match g.check with
      | [] =>
        let claims := (derived g.rules).map (fun c =>
          (⟨c.text, c.grounds, "proved", "CardGen.derived_valid"⟩ : ClaimOut)) ++
          (gameClaims g).map (fun c => (⟨c.text, c.grounds, "proved", "CardGen.gameClaims_valid"⟩ : ClaimOut)) ++
          turnClaims g.rules g.cards ++
          (attackClaim g.cards).toList
        ⟨1, true, [], claims, some (negOut g.rules g.cards)⟩
      | es => fail es

def statusLabel : String → String
  | "proved" => "証明済み"
  | "counterexample" => "反例あり"
  | "choice" => "プレイヤーの選択"
  | _ => "未確定"

/-- 人が読む形 -/
def Report.toText (r : Report) : String :=
  if !r.ok then
    "形式の誤りがあります：\n" ++ "\n".intercalate (r.errors.map ("- " ++ ·))
  else
    let claims := r.claims.map fun c =>
      s!"- [{statusLabel c.status}] {c.text}\n    根拠：{"、".intercalate c.grounds}"
    let side (c : SideCard) : String := (if c.side == "self" then "自分：" else "相手：") ++ c.card
    let neg := match r.negation with
      | some n =>
        let gs := n.groups.map fun g =>
          s!"\n    循環：{" ⇄ ".intercalate g.cards}\n      [{statusLabel g.status}] {g.message}" ++
          (if g.board.isEmpty then "" else s!"\n      盤面：{"、".intercalate (g.board.map side)}") ++
          (if g.detail.isEmpty then "" else s!"\n      参考：{g.detail}")
        s!"- [{statusLabel n.status}] {n.message}{String.join gs}"
      | none => ""
    "★ ルールから導いた性質\n" ++ "\n".intercalate claims ++ "\n\n無効の関係\n" ++ neg

end CardGen
