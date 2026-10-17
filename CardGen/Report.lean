import CardGen.Explore

/-!
# 検査ツールの報告

中間表現の JSON を受け取り、次をまとめて返す。

- `errors`：形式の誤り（あれば★と無効の検査は行わない）
- `claims`：ルールから導いた★。どれも `CardGen.derived_valid` で証明済み
- `negation`：無効の関係の検査。循環がなければ `CardGen.negation_settles` で証明済み。
  循環があれば、まとまりごとに小さな盤面を総当たりで調べた結果（`CardGen.exploreGroup`）

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

def groupOut (g : GroupResult) : GroupOut :=
  let board := g.board.map fun (c, mine) => (⟨c, if mine then "self" else "opp"⟩ : SideCard)
  let (status, message) : String × String := match g.verdict with
    | none => ("unknown", s!"カードが{exploreLimit}枚を超えるため、総当たりで調べていません")
    | some .ok => ("unknown",
        "各カードを自分・相手に1枚ずつまで置いた盤面では問題は見つかりませんでした（それより多い盤面は調べていません）")
    | some .someLoop => ("choice",
        "この盤面では、結果は1通りですが、選び方によって判定が回り続けます（止まる選び方はあります）")
    | some .multiStable => ("choice",
        "この盤面では、安定な状態が複数あり、適用の順番で結果が変わります（先に適用された方を優先するなどの規則が必要です）")
    | some .cannotHalt => ("counterexample", "この盤面では、どう選んでも判定が止まらない状態があります")
    | some .noStable => ("counterexample", "この盤面では、どの状態も安定せず、判定が止まりません")
  ⟨g.cards, status, message, board⟩

def statusSeverity : String → Nat
  | "counterexample" => 3
  | "unknown" => 2
  | "choice" => 1
  | _ => 0

def negOut (cards : List Card) : NegOut :=
  let edges := (negEdges cards).map fun (a, b) => [a, b]
  match checkNegation cards with
  | .none => ⟨"proved", "無効にする効果を持つカードはありません", edges, [], none⟩
  | .proved =>
    ⟨"proved", "無効にしうる関係に循環はありません。どの盤面でも、無効の判定はどの順番で進めても必ず止まり、結果は1通りです",
      edges, [], some "CardGen.negation_settles"⟩
  | .cyclic gs =>
    let groups := gs.map fun names =>
      groupOut (exploreGroup (names.filterMap fun nm => cards.find? (·.name == nm)))
    let worst := groups.foldl (fun w g => if statusSeverity g.status > statusSeverity w then g.status else w) "choice"
    ⟨worst, "無効にしうる関係に循環があります。循環のまとまりごとに、小さな盤面を総当たりで調べました",
      edges, groups, none⟩

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
        let claims := (derived g.rules).map fun c =>
          (⟨c.text, c.grounds, "proved", "CardGen.derived_valid"⟩ : ClaimOut)
        ⟨1, true, [], claims, some (negOut g.cards)⟩
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
          (if g.board.isEmpty then "" else s!"\n      盤面：{"、".intercalate (g.board.map side)}")
        s!"- [{statusLabel n.status}] {n.message}{String.join gs}"
      | none => ""
    "★ ルールから導いた性質\n" ++ "\n".intercalate claims ++ "\n\n無効の関係\n" ++ neg

end CardGen
