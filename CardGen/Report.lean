import CardGen.Negation

/-!
# 検査ツールの報告

中間表現の JSON を受け取り、次をまとめて返す。

- `errors`：形式の誤り（あれば★と無効の検査は行わない）
- `claims`：ルールから導いた★。どれも `CardGen.derived_valid` で証明済み
- `negation`：無効の関係の検査。循環がなければ `CardGen.negation_settles` で証明済み、
  循環があれば未確定（総当たりによる第3層の検査は今後）

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

structure NegOut where
  status : String
  message : String
  edges : List (List String)
  cycles : List (List String)
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

def negOut (cards : List Card) : NegOut :=
  let edges := (negEdges cards).map fun (a, b) => [a, b]
  match checkNegation cards with
  | .none => ⟨"proved", "無効にする効果を持つカードはありません", edges, [], none⟩
  | .proved =>
    ⟨"proved", "無効にしうる関係に循環はありません。どの盤面でも、無効の判定はどの順番で進めても必ず止まり、結果は1通りです",
      edges, [], some "CardGen.negation_settles"⟩
  | .cyclic gs =>
    ⟨"unknown", "無効にしうる関係に循環があります。このまとまりの中では、適用の順番で結果が変わったり、判定が止まらなかったりする可能性があります（総当たりによる検査は未実装）",
      edges, gs, none⟩

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
    let neg := match r.negation with
      | some n =>
        let cyc := n.cycles.map fun g => s!"\n    循環：{" ⇄ ".intercalate g}"
        s!"- [{statusLabel n.status}] {n.message}{String.join cyc}"
      | none => ""
    "★ ルールから導いた性質\n" ++ "\n".intercalate claims ++ "\n\n無効の関係\n" ++ neg

end CardGen
