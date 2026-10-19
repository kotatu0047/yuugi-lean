import CardGen.TurnProps
import CardGen.Negation

/-!
# 形式の警告の裏付け

形式の検査（`Game.check`、`IR.lean`）の警告のうち、「書いても意味がない」ことを言うものについて、
その意味を対戦のモデルの上で証明する。盤面の制約や★の定理は形式の検査が通ることを前提にしないので、
警告は「定理が崩れる」ことではなく、「その部分は対戦で何も起こさない（だから書き間違いだろう）」ことを示す。

| 警告 | 裏付けの定理 |
| --- | --- |
| 範囲のカードの種類が空です | `Selector.matches_eq_false_of_types_nil`（どのカードにも当たらない） |
| 範囲のカードの種類「…」はルールにありません | `Selector.matches_known_types`（除いても、ルールにある種類のカードへの当たり方は同じ） |
| 範囲のタグ「…」はどのタグの集合にもありません | `Selector.matches_eq_false_of_unknown_tag`（タグが集合にあるカードには当たらない） |
| ドローの枚数・ダメージ・回復する量が0です | `State.applyAction_draw_zero` など（盤面は変わらない） |
| カードへのダメージが0です／範囲に戦闘できる種類がありません | `State.strike_eq_sweep`（状態の確認と同じで、ダメージを与えない） |
| ターンの終わりまでの変化が0です／範囲に戦闘できる種類がありません | `State.pumpAll_eq_sweep`（同上） |
| 打ち消す範囲の種類を、「フィールド上」でないゾーンに置けません | `State.counter_eq_self`（到達できる盤面では何もしない） |
| 攻撃力・守備力の変化が0です | `modTerm_boost_zero`・`modTerm_toughen_zero`（加える量は0） |
| 攻撃力・守備力を変える範囲に、戦闘できる種類のカードがありません | `modTerm_boost_nonfighter` など（戦闘できるカードには0） |
| 永続効果の範囲では、対象を選べません | `modTerm_boost_target` など・`Selector.matches_negView_target`（何にも当たらない） |
| 発動する効果に動きがありません | `State.resolve_nil`（無効にされて解決したのと同じ） |
| 誘発する効果に動きがありません | `State.fire_nil`（解決しても盤面は変わらない） |
| カードの種類「…」はルールにありません | `Reachable.type_known`（ゾーンの検査が通れば、そのカードはどの盤面でもフィールドに出ない） |
| ゾーンのマスの数が0です／置けるカードの種類が空です | `Reachable.zone_used`（そのゾーンにはどの盤面でもカードがない） |
| マナの色があるのに（選べる色があるのに）、出るマナの量が0です | `manaOut_eq_nil`（タップしてもマナは出ない） |
| 「…」を置ける枚数の上限が0です | `TReachable.placed_none`（その種類は1枚も置けない） |
| 初期手札がデッキの枚数より多いです | `start_hand_length`（初期手札はデッキの枚数までしか引けない） |
| 戦闘できる種類があるのに、初期ライフが0です | `Match.over_life_zero`（ライフで対戦が終わることはない） |

重複・版・役割のゾーンの数などの残りの警告は、中間表現の書き方の決まり（どれを指すかが一意でない、など）である。
-/

namespace CardGen

/-! ## 範囲 -/

/-- **種類が空の範囲は、どのカードにも当たらない** -/
theorem Selector.matches_eq_false_of_types_nil {s : Selector} (h : s.types = []) (v : View) :
    s.matches v = false := by
  simp [Selector.matches, h]

/-- **ルールにない種類を範囲から除いても、ルールにある種類のカードへの当たり方は変わらない**
（ルールにない種類は、ルールにある種類のカードには当たらない） -/
theorem Selector.matches_known_types (r : Rules) (s : Selector) (v : View) (hv : v.type ∈ r.cardTypes) :
    { s with types := s.types.filter (r.cardTypes.contains ·) }.matches v = s.matches v := by
  simp [Selector.matches, List.mem_filter, hv]

theorem mem_unknownTags {r : Rules} {l : List String} {t : String} :
    t ∈ r.unknownTags l ↔ r.tagSets ≠ [] ∧ t ∈ l ∧ t ∉ r.allTags := by
  unfold Rules.unknownTags
  by_cases h : r.tagSets = []
  · simp [h]
  · simp [h, List.mem_eraseDups, List.mem_filter]

/-- 形式の検査でタグの警告が出ないカードは、タグがどれもタグの集合にある（タグの集合があるとき） -/
theorem tags_known {r : Rules} {l : List String} (hs : r.tagSets ≠ []) (h : r.unknownTags l = []) :
    ∀ x ∈ l, x ∈ r.allTags := by
  intro x hx
  refine Classical.byContradiction fun hn => ?_
  have : x ∈ r.unknownTags l := mem_unknownTags.2 ⟨hs, hx, hn⟩
  simp [h] at this

/-- **どのタグの集合にもないタグを持つ範囲は、タグがどれも集合にあるカードに当たらない**
（形式の検査が通るカードは、そのようなカード：`tags_known`） -/
theorem Selector.matches_eq_false_of_unknown_tag {r : Rules} {s : Selector} {t : String} {v : View}
    (ht : t ∈ r.unknownTags s.tags) (hv : ∀ x ∈ v.tags, x ∈ r.allTags) : s.matches v = false := by
  obtain ⟨-, hts, hu⟩ := mem_unknownTags.1 ht
  have : s.tags.all v.tags.contains = false := by
    rw [List.all_eq_false]
    exact ⟨t, hts, fun h => hu (hv t (List.contains_iff_mem.1 h))⟩
  simp [Selector.matches, this]

/-! ## 発動する効果の動き -/

theorem State.set_self (g : State) (p : PlayerId) : g.set p (g p) = g := by
  funext q; cases p <;> cases q <;> rfl

/-- **0枚引く動きは、盤面を変えない** -/
theorem State.applyAction_draw_zero (r : Rules) (src : Src) (negS) (g : State) :
    g.applyAction r src negS (.draw 0) = g := by
  simp only [State.applyAction, PState.drawN, List.drop_zero, List.take_zero, List.append_nil]
  exact State.set_self g src.p

/-- **0のダメージは、盤面を変えない** -/
theorem State.applyAction_damage_zero (r : Rules) (src : Src) (negS) (g : State) :
    g.applyAction r src negS (.damage 0) = g := by
  simp only [State.applyAction, PState.damage, Nat.sub_zero]
  exact State.set_self g (!src.p)

/-- **0の回復は、盤面を変えない** -/
theorem State.applyAction_heal_zero (r : Rules) (src : Src) (negS) (g : State) :
    g.applyAction r src negS (.heal 0) = g := by
  simp only [State.applyAction, Nat.add_zero]
  exact State.set_self g src.p

theorem PState.mark_eq_self {d : Nat → Nat} {s : PState} (h : ∀ i, i < s.field.length → d i = 0) : s.mark d = s := by
  cases s with
  | mk deck hand grave field life =>
    simp only [PState.mark, PState.mk.injEq, true_and, and_true]
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp [h i h2]

theorem PState.pump_eq_self {d : Nat → Int × Int} {s : PState} (h : ∀ i, i < s.field.length → d i = (0, 0)) :
    s.pump d = s := by
  cases s with
  | mk deck hand grave field life =>
    simp only [PState.pump, PState.mk.injEq, true_and, and_true]
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp [h i h2]

/-- 範囲に戦闘できる種類がなければ、戦闘できるカードは範囲に当たらない -/
theorem not_fights_and_matches {r : Rules} {sel : Selector} (h : sel.types.any r.fighters.contains = false)
    (sl : Slot) (q : PlayerId) (src : Src) : (r.fights sl && sel.matches (sl.view r q src)) = false := by
  rw [List.any_eq_false] at h
  cases hf : r.fights sl <;> cases hm : sel.matches (sl.view r q src) <;> simp
  simp only [Rules.fights, Bool.and_eq_true] at hf
  simp only [Selector.matches, Bool.and_eq_true] at hm
  exact h _ (List.contains_iff_mem.1 hm.1.1.1.1.1.1) hf.2

theorem State.strikeMarks_eq_self (r : Rules) (sel : Selector) (n : Nat) (src : Src) (g : State)
    (h : n = 0 ∨ sel.types.any r.fighters.contains = false) : g.strikeMarks r sel n src = g := by
  funext q
  simp only [State.strikeMarks, State.map_apply]
  apply PState.mark_eq_self
  intro i hi
  rw [List.getElem?_eq_getElem hi]
  simp only
  rcases h with h | h
  · split <;> simp [h]
  · rw [not_fights_and_matches h]; rfl

/-- **ダメージが0か、範囲に戦闘できる種類がないカードへのダメージは、状態の確認と同じ**
（どのカードにもダメージを与えない。すでに守備力以上のダメージを受けているカードが破壊されるだけ：`Step.settle`） -/
theorem State.strike_eq_sweep (r : Rules) (sel : Selector) (n : Nat) (src : Src) (negS) (g : State)
    (h : n = 0 ∨ sel.types.any r.fighters.contains = false) :
    g.strike r sel n src negS = g.sweep r (g.negAt negS) := by
  simp only [State.strike, State.strikeMarks_eq_self r sel n src g h]

theorem State.pumpMarks_eq_self (r : Rules) (sel : Selector) (a d : Int) (src : Src) (g : State)
    (h : (a = 0 ∧ d = 0) ∨ sel.types.any r.fighters.contains = false) : g.pumpMarks r sel a d src = g := by
  funext q
  simp only [State.pumpMarks, State.map_apply]
  apply PState.pump_eq_self
  intro i hi
  rw [List.getElem?_eq_getElem hi]
  simp only
  rcases h with ⟨ha, hd⟩ | h
  · split <;> simp [ha, hd]
  · rw [not_fights_and_matches h]; rfl

/-- **変化が攻撃力・守備力とも0か、範囲に戦闘できる種類がないターンの終わりまでの変化は、状態の確認と同じ** -/
theorem State.pumpAll_eq_sweep (r : Rules) (sel : Selector) (a d : Int) (src : Src) (negS) (g : State)
    (h : (a = 0 ∧ d = 0) ∨ sel.types.any r.fighters.contains = false) :
    g.pumpAll r sel a d src negS = g.sweep r (g.negAt negS) := by
  simp only [State.pumpAll, State.pumpMarks_eq_self r sel a d src g h]

/-- 打ち消す範囲の種類のどれも、「フィールド上」でない普通のゾーンに置けない -/
def Rules.counterless (r : Rules) (sel : Selector) : Prop :=
  sel.types.any (fun t => r.zones.any fun z => z.role == .plain && !z.onField && z.admits.contains t) = false

/-- **打ち消す範囲の種類を「フィールド上」でないゾーンに置けなければ、到達できる盤面で打ち消しは何もしない** -/
theorem State.counter_eq_self {r : Rules} {g : State} (hinv : Inv r g) {sel : Selector} (h : r.counterless sel)
    (src : Src) : g.applyAction r src negS (.counter sel) = g := by
  have hno : ∀ q, ∀ sl ∈ (g q).field, (!r.onFieldZone sl.zone && sel.matches (sl.view r q src)) = false := by
    intro q sl hsl
    obtain ⟨z, hz, hrole, hadm, -⟩ := hinv.zones q sl hsl
    unfold Rules.counterless at h
    rw [List.any_eq_false] at h
    cases hm : sel.matches (sl.view r q src)
    · simp
    · simp only [Selector.matches, Bool.and_eq_true] at hm
      have hon : r.onFieldZone sl.zone = z.onField := by simp [Rules.onFieldZone, hz, hrole]
      cases hof : z.onField
      · exfalso
        apply h _ (List.contains_iff_mem.1 hm.1.1.1.1.1.1)
        rw [List.any_eq_true]
        exact ⟨z, List.mem_of_getElem? hz, by simp [hrole, hof, Slot.view]; exact List.contains_iff_mem.1 hadm⟩
      · simp [hon, hof]
  funext q
  show (g.map fun q s => s.counter r sel q src) q = g q
  rw [State.map_apply]
  have hno' := hno q
  cases hq : g q with
  | mk deck hand grave field life =>
    rw [hq] at hno'
    have e1 : field.filter (fun sl => !(!r.onFieldZone sl.zone && sel.matches (sl.view r q src))) = field :=
      List.filter_eq_self.2 fun sl hsl => by simp [hno' sl hsl]
    have e2 : field.filter (fun sl => !r.onFieldZone sl.zone && sel.matches (sl.view r q src)) = [] :=
      List.filter_eq_nil_iff.2 fun sl hsl => by simp [hno' sl hsl]
    show PState.mk deck hand (grave ++ _) _ life = _
    rw [e1, e2]
    simp

/-- **動きのない発動する効果を解決するのは、無効にされて解決したのと同じ**（カードが墓地へ送られるだけ） -/
theorem State.resolve_nil (r : Rules) (p : PlayerId) (g : State) (k : Nat) (sl : Slot) (apply : Bool) (neg tgt) :
    g.resolve r p k sl [] apply neg tgt = g.resolve r p k sl [] false neg tgt := by
  cases apply <;> rfl

/-- **動きのない誘発する効果は、解決しても盤面を変えない** -/
theorem State.fire_nil (r : Rules) (p : PlayerId) (g : State) (cell : Option Cell) (apply : Bool) (neg tgt) :
    g.fire r p [] cell apply neg tgt = g := by
  cases apply <;> rfl

/-! ## 永続効果（攻撃力・守備力の変化と無効） -/

/-- 永続効果 `e` の1つが、位置 `t` のカード `tsl` の値に加える量（`modFrom` の中身） -/
def modTerm (r : Rules) (pick : Effect → Option (Selector × Int)) (t : Pos) (tsl : Slot) (q : PlayerId) (j : Nat)
    (src : Slot) (e : Effect) : Int :=
  match pick e with
  | some (sel, n) => if sel.matches { tsl.view r t.1 ⟨q, r.cellOf q src, none⟩ with isSelf := (q, j) == t } then n else 0
  | none => 0

/-- カードの効果が値に加える量は、効果ごとの量の和 -/
theorem modFrom_eq (r : Rules) (pick) (neg : List Pos) (t : Pos) (tsl : Slot) (q : PlayerId) (j : Nat) (src : Slot) :
    modFrom r pick neg t tsl q j src =
      if src.faceUp && r.onFieldZone src.zone && !neg.contains (q, j) then
        (src.card.effects.map (modTerm r pick t tsl q j src)).sum else 0 := rfl

/-- **攻撃力の変化が0の効果は、どのカードの攻撃力にも何も加えない** -/
theorem modTerm_boost_zero (r : Rules) (s : Selector) (t tsl q j src) :
    modTerm r Effect.atkMod t tsl q j src (.boost s 0) = 0 := by
  simp [modTerm, Effect.atkMod]

/-- **守備力の変化が0の効果は、どのカードの守備力にも何も加えない** -/
theorem modTerm_toughen_zero (r : Rules) (s : Selector) (t tsl q j src) :
    modTerm r Effect.defMod t tsl q j src (.toughen s 0) = 0 := by
  simp [modTerm, Effect.defMod]

/-- 永続効果の範囲から見るカードは、対象ではない -/
theorem matches_permanent_target {r : Rules} {s : Selector} (hs : s.target = true) (tsl : Slot) (t : Pos) (q : PlayerId)
    (c : Option Cell) (b : Bool) : s.matches { tsl.view r t.1 ⟨q, c, none⟩ with isSelf := b } = false := by
  simp [Selector.matches, hs, Slot.view]

/-- **対象を選ぶ範囲の攻撃力の変化は、何にも当たらない** -/
theorem modTerm_boost_target (r : Rules) {s : Selector} (hs : s.target = true) (n t tsl q j src) :
    modTerm r Effect.atkMod t tsl q j src (.boost s n) = 0 := by
  simp only [modTerm, Effect.atkMod, matches_permanent_target hs]; rfl

/-- **対象を選ぶ範囲の守備力の変化は、何にも当たらない** -/
theorem modTerm_toughen_target (r : Rules) {s : Selector} (hs : s.target = true) (n t tsl q j src) :
    modTerm r Effect.defMod t tsl q j src (.toughen s n) = 0 := by
  simp only [modTerm, Effect.defMod, matches_permanent_target hs]; rfl

theorem matches_nonfighter {r : Rules} {s : Selector} (hs : s.types.any r.fighters.contains = false) {tsl : Slot}
    (ht : r.fighters.contains tsl.card.type = true) (t : Pos) (q : PlayerId) (c : Option Cell) (b : Bool) :
    s.matches { tsl.view r t.1 ⟨q, c, none⟩ with isSelf := b } = false := by
  rw [List.any_eq_false] at hs
  cases hm : s.matches { tsl.view r t.1 ⟨q, c, none⟩ with isSelf := b }
  · rfl
  · simp only [Selector.matches, Bool.and_eq_true] at hm
    exact absurd ht (hs _ (List.contains_iff_mem.1 hm.1.1.1.1.1.1))

/-- **範囲に戦闘できる種類がない攻撃力の変化は、戦闘できるカードの攻撃力に何も加えない** -/
theorem modTerm_boost_nonfighter (r : Rules) {s : Selector} (hs : s.types.any r.fighters.contains = false) {tsl : Slot}
    (ht : r.fighters.contains tsl.card.type = true) (n t q j src) :
    modTerm r Effect.atkMod t tsl q j src (.boost s n) = 0 := by
  simp only [modTerm, Effect.atkMod, matches_nonfighter hs ht]; rfl

/-- **範囲に戦闘できる種類がない守備力の変化は、戦闘できるカードの守備力に何も加えない** -/
theorem modTerm_toughen_nonfighter (r : Rules) {s : Selector} (hs : s.types.any r.fighters.contains = false) {tsl : Slot}
    (ht : r.fighters.contains tsl.card.type = true) (n t q j src) :
    modTerm r Effect.defMod t tsl q j src (.toughen s n) = 0 := by
  simp only [modTerm, Effect.defMod, matches_nonfighter hs ht]; rfl

/-- **無効の範囲で対象を選んでも、無効の関係では何にも当たらない** -/
theorem Selector.matches_negView_target {s : Selector} (hs : s.target = true) (b a : Inst) (isSelf : Bool) :
    s.matches (b.viewFrom a isSelf) = false := by
  simp [Selector.matches, hs, Inst.viewFrom]

/-! ## カード・ゾーン・ルール -/

/-- **ゾーンに置ける種類がどれもルールのカードの種類なら（ゾーンの検査が通れば）、到達できる盤面のフィールドのカードは、
種類がルールにある**（ルールにない種類のカードは、フィールドに出ない） -/
theorem Reachable.type_known {r : Rules} {decks : PlayerId → List Card} (hd : ∀ p, (decks p).length = r.deckSize)
    {g : State} (h : Reachable r decks g) (hz : ∀ z ∈ r.zones, ∀ t ∈ z.admits, t ∈ r.cardTypes)
    {p : PlayerId} {sl : Slot} (hsl : sl ∈ (g p).field) : sl.card.type ∈ r.cardTypes := by
  obtain ⟨z, hzi, -, hadm, -⟩ := (h.inv hd).zones p sl hsl
  exact hz z (List.mem_of_getElem? hzi) _ (List.contains_iff_mem.1 hadm)

/-- **到達できる盤面でカードがあるゾーンは、マスの数が1以上で、置ける種類がある**
（マスの数が0のゾーンや、置ける種類が空のゾーンには、カードは置かれない） -/
theorem Reachable.zone_used {r : Rules} {decks : PlayerId → List Card} (hd : ∀ p, (decks p).length = r.deckSize)
    {g : State} (h : Reachable r decks g) {p : PlayerId} {sl : Slot} (hsl : sl ∈ (g p).field) {z : Zone}
    (hz : r.zones[sl.zone]? = some z) : 0 < z.count ∧ z.admits ≠ [] := by
  obtain ⟨z', hz', -, hadm, hc⟩ := (h.inv hd).zones p sl hsl
  rw [hz] at hz'
  cases hz'
  refine ⟨Nat.lt_of_le_of_lt (Nat.zero_le _) hc, ?_⟩
  intro he
  simp [he] at hadm

/-- **出るマナの量が0のカードは、タップしてもマナが出ない** -/
theorem manaOut_eq_nil {c : Card} (h : c.mana = 0) {color : String} {out : List String}
    (ho : manaOut c color = some out) : out = [] := by
  unfold manaOut at ho
  split at ho
  · cases ho; simp [h]
  · split at ho
    · cases ho; simp [h]
    · cases ho

/-- **置ける枚数の上限が0の種類のカードは、どのターンにも1枚も置けない**（そのターンに置いたカードの種類の記録に出ない） -/
theorem TReachable.placed_none {r : Rules} {decks : PlayerId → List Card} {first : PlayerId} {m : Match}
    (h : TReachable r decks first m) {l : PlaceLimit} (hl : l ∈ r.placeLimits) (h0 : l.count = 0) :
    ∀ t ∈ m.turn.placed, l.types.contains t = false := by
  have := h.placed_le hl
  rw [h0, Nat.le_zero, List.length_eq_zero_iff, List.filter_eq_nil_iff] at this
  intro t ht
  simpa using this t ht

/-- **初期手札は、デッキにある枚数までしか引けない**（初期手札がデッキの枚数より多ければ、その枚数にはならない） -/
theorem start_hand_length (r : Rules) (decks : PlayerId → List Card) (p : PlayerId) :
    (start r decks p).hand.length = min r.handSize (decks p).length := by
  simp [start, List.length_take]

/-- **初期ライフが0なら、ライフで対戦が終わることはない**（終わるのはデッキ切れだけ） -/
theorem Match.over_life_zero {r : Rules} (h : r.life = 0) (m : Match) : m.over r = m.turn.decked.isSome := by
  simp [Match.over, h]

end CardGen
