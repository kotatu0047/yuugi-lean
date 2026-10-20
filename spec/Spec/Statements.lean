import CardGen

/-!
# 凍結した主張（人がレビューする仕様）

レポート（`CardGen/Report.lean`）が「証明済み」として名前を出す定理の主張を、ここに書き写して凍結する。
`Spec/Check.lean` が、`CardGen` の定理の型がこの主張とちょうど一致すること、使う公理が標準の3つだけであることを
検査する。

- このファイルは人がレビューして変える。エージェントは変えない（`.claude/settings.json` で書き込みを禁止）
- 主張に出てくる定義（`Reachable`・`Step`・`Match.step?` など）は `CardGen` 側にある。定義を変えると主張の意味も
  変わるので、モデルの定義の変更は別にレビューする（`CLAUDE.md`）
-/

namespace Spec
open CardGen

/-! ## ★を出す定理 -/

/-- ルールから導く★は、デッキの枚数がルールどおりなら、どの対戦でも成り立つ -/
def derived_valid : Prop :=
  ∀ (r : Rules) (decks : PlayerId → List Card), (∀ p, (decks p).length = r.deckSize) →
    ∀ c ∈ derived r, c.prop.Valid r decks

/-- カードの一覧によって決まる★は、一覧のカードで作ったどのデッキでも成り立つ -/
def gameClaims_valid : Prop :=
  ∀ (g : Game) (decks : PlayerId → List Card), (∀ p, ∀ x ∈ decks p, x ∈ g.cards) →
    (∀ p, (decks p).length = g.rules.deckSize) → ∀ c ∈ gameClaims g, c.prop.Valid g.rules decks

/-- 無効の関係に循環がなければ、判定は必ず止まり、結果は1通り -/
def negation_settles : Prop :=
  ∀ {cards : List Card} {rank : Card → Nat}, rankOK cards rank = true →
    ∀ (insts : List Inst), (∀ a ∈ insts, a.card ∈ cards) →
      let S := System.ofInsts insts
      WellFounded (fun g f => S.Step f g) ∧ (∃ f, S.Stable f) ∧
      ∀ f g, S.Stable f → S.Stable g → ∀ x < S.n, f x = g x

/-- 証明書が通れば、時刻つきの判定はどう選んでも止まり、結果は1通り -/
def allEnd_of_certOK : Prop :=
  ∀ (S : TSys) {tp : Bool} {pot : TState → Nat} {res : TState → List Bool},
    S.certOK tp pot res = true → ∀ s, S.Valid s → S.TAllEnd tp (res s) s

/-- 実行できる1歩は、証明に使う動きの関係と一致する -/
def step?_sound : Prop :=
  ∀ {r : Rules} {g g' : State} {ch : Choice}, g.step? r ch = some g' → Step r g g'

/-! ## カードの流れ -/

def cards_perm : Prop :=
  ∀ {r : Rules} {decks : PlayerId → List Card} {g : State}, Reachable r decks g →
    ∀ (p : PlayerId), (g p).cards.Perm (decks p)

def deck_suffix : Prop :=
  ∀ {r : Rules} {decks : PlayerId → List Card} {g : State}, Reachable r decks g →
    ∀ (p : PlayerId), (g p).deck <:+ (decks p).drop r.handSize

def grave_prefix : Prop :=
  ∀ {r : Rules} {g g' : State}, Step r g g' → ∀ (p : PlayerId), (g p).grave <+: (g' p).grave

def step?_grave_prefix : Prop :=
  ∀ {r : Rules} {m m' : Match} {ch : TChoice}, m.step? r ch = some m' →
    ∀ (p : PlayerId), (m.g p).grave <+: (m'.g p).grave

/-! ## ターンのある対戦 -/

def of_reachable : Prop :=
  ∀ {r : Rules} {decks : PlayerId → List Card} {first : PlayerId} {m : Match} {P : State → Prop},
    (∀ g, Reachable r decks g → P g) → TReachable r decks first m → P m.g

def summons_le : Prop :=
  ∀ {r : Rules} {decks : PlayerId → List Card} {first : PlayerId} {m : Match},
    TReachable r decks first m → r.summonsPerTurn ≠ 0 → m.turn.summons ≤ r.summonsPerTurn

def placed_le : Prop :=
  ∀ {r : Rules} {decks : PlayerId → List Card} {first : PlayerId} {m : Match},
    TReachable r decks first m → ∀ {l : PlaceLimit}, l ∈ r.placeLimits →
      (m.turn.placed.filter l.types.contains).length ≤ l.count

def fits : Prop :=
  ∀ {r : Rules} {decks : PlayerId → List Card} {first : PlayerId} {m : Match},
    TReachable r decks first m → m.turn.Fits m.g

def attacked_bagLe : Prop :=
  ∀ {r : Rules} {decks : PlayerId → List Card} {first : PlayerId} {m : Match},
    TReachable r decks first m → BagLe m.turn.attacked (m.g m.turn.tp).bases

def spent_le : Prop :=
  ∀ {r : Rules} {decks : PlayerId → List Card} {first : PlayerId} {m : Match},
    TReachable r decks first m → m.turn.spent ≤ m.turn.made

def stack_fits : Prop :=
  ∀ {r : Rules} {decks : PlayerId → List Card} {first : PlayerId} {m : Match},
    TReachable r decks first m → m.turn.StackFits m.g

def mana_from : Prop :=
  ∀ {r : Rules} {decks : PlayerId → List Card} {first : PlayerId} {m : Match} {pool : List Card},
    (∀ p, ∀ x ∈ decks p, x ∈ pool) → TReachable r decks first m →
      ∀ c ∈ m.turn.pool ++ m.turn.oppPool, ManaFrom pool c

def pending_triggered : Prop :=
  ∀ {r : Rules} {decks : PlayerId → List Card} {first : PlayerId} {m : Match},
    TReachable r decks first m → ∀ e ∈ m.turn.pending, e.Triggered

def step?_over : Prop :=
  ∀ {r : Rules} {m : Match}, m.over r = true → ∀ (ch : TChoice), m.step? r ch = none

def endTurn_clean : Prop :=
  ∀ {r : Rules} {m m' : Match}, m.step? r .endTurn = some m' → ∀ q, ∀ sl ∈ (m'.g q).field, sl.base = sl

def endTurn_hand : Prop :=
  ∀ {r : Rules} {m m' : Match}, m.step? r .endTurn = some m' → r.handLimit ≠ 0 →
    (m.g m.turn.tp).hand.length ≤ r.handLimit

def step?_pending : Prop :=
  ∀ {r : Rules} {m : Match}, m.turn.pending ≠ [] → ∀ {ch : TChoice}, (∀ neg, ch ≠ .settle neg) →
    (∀ i sk a neg tgt, ch ≠ .trigger i sk a neg tgt) → m.step? r ch = none

def step?_prio : Prop :=
  ∀ {r : Rules} {m m' : Match} {ch : TChoice}, m.step? r ch = some m' → ch ≠ .pass →
    (∀ neg, ch ≠ .settle neg) → (∀ i sk a neg tgt, ch ≠ .trigger i sk a neg tgt) →
    m.turn.afterPasses r ch = false → ch.actor m.turn.tp = m.turn.prio

end Spec
