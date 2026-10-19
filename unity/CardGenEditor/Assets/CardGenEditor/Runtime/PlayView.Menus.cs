using System;
using System.Collections.Generic;
using System.Linq;
using UnityEngine;

namespace CardGen.App
{
    /// <summary>
    /// テストプレイの右クリックのメニュー：手札・場のカード、空きのマス、プレイヤーの盤面、盤面と右の欄の空き場所
    /// </summary>
    public sealed partial class PlayView
    {
        /// <summary>ターンを終えられるか（攻撃の途中でもスタックがあるのでもなく、ターンプレイヤーが優先権を持つ）</summary>
        bool CanEndTurn => match.Turn.Quiet && !match.Over(game.Rules) && match.Turn.Prio == turn && match.Turn.Passes < 2 &&
                           Match.HandOK(game.Rules, state, turn) && match.Turn.Pending.Count == 0;

        /// <summary>ターンを終えられない理由（終えられるなら null）</summary>
        string EndTurnBlocked()
        {
            var t = match.Turn;
            if (match.Over(game.Rules)) return "対戦は終わっています";
            if (t.Pending.Count > 0) return "誘発した効果の待ちがあります（解決してから）";
            if (t.Stack.Count > 0) return "スタックにカードがあります（解決してから）";
            if (t.Attackers.Count > 0) return "攻撃の途中です（ブロックを選んでから）";
            if (t.Prio != turn) return $"優先権が{Who(t.Prio)}にあります（{Who(t.Prio)}がパスしてから）";
            if (t.Passes >= 2) return "両者がパスした直後です";
            if (OverHand > 0) return $"手札が上限（{game.Rules.HandLimit} 枚）を超えています（あと {OverHand} 枚捨ててから）";
            return null;
        }

        // ---- カードの詳細 ----

        static string EffectText(Effect e) => e switch
        {
            Activated a => "発動：" + (a.Actions.Count == 0 ? "（動きなし）" : string.Join(" → ", a.Actions.Select(ActionText))),
            Negate n => "永続：" + NodeView.SelectorSummary(n.Target).Replace("\n", "・") + "の効果を無効",
            Boost b => "永続：" + NodeView.SelectorSummary(b.Target).Replace("\n", "・") + $"の攻撃力 {(b.Amount >= 0 ? "+" : "")}{b.Amount}",
            Toughen t => "永続：" + NodeView.SelectorSummary(t.Target).Replace("\n", "・") + $"の守備力 {(t.Amount >= 0 ? "+" : "")}{t.Amount}",
            _ => "",
        };

        /// <summary>カードそのものの詳細（種類・タグ・コスト・マナ・攻守・能力・効果）</summary>
        List<MenuEntry> CardInfo(Card c, bool stats = true)
        {
            var items = new List<MenuEntry> { MenuEntry.Header("詳細") };
            items.Add(MenuEntry.Info($"種類：{c.Type}" + (c.Tags.Count > 0 ? $"・タグ：{string.Join("・", c.Tags)}" : "")));
            if (UsesMana && (c.Cost > 0 || c.ColorCost.Count > 0)) items.Add(MenuEntry.Info($"コスト：{CostText(c)}"));
            if (c.Mana > 0) items.Add(MenuEntry.Info($"タップ：{ManaText(c)}"));
            var kw = new[] { c.Trample ? "トランプル" : null, c.Flying ? "飛行" : null, c.Reach ? "到達" : null }.Where(x => x != null).ToList();
            if (stats && (c.Attack > 0 || c.Defense > 0 || game.Rules.Fighters.Contains(c.Type)))
                items.Add(MenuEntry.Info($"攻撃力 {c.Attack}・守備力 {c.Defense}" + (kw.Count > 0 ? "・" + string.Join("・", kw) : "")));
            else if (kw.Count > 0) items.Add(MenuEntry.Info(string.Join("・", kw)));
            if (TurnInfo.Instant(game.Rules, c)) items.Add(MenuEntry.Info("いつでも置ける（相手のターンや応答として）"));
            foreach (var e in c.Effects) items.Add(MenuEntry.Info(EffectText(e)));
            if (c.Effects.Count == 0) items.Add(MenuEntry.Info("効果なし"));
            return items;
        }

        // ---- 手札のカード ----

        /// <summary>p の手札の i 番目の右クリックのメニュー：そのカードを選び、右の欄と同じ動きと、詳細を出す</summary>
        public List<MenuEntry> HandMenu(bool p, int i)
        {
            SelectHand(p, i);
            var c = state.Get(p).Hand[i];
            var items = new List<MenuEntry>
            {
                MenuEntry.Title(c.Name, $"{Who(p)}の手札・{c.Type}" + (UsesMana ? $"・コスト {CostText(c)}" : ""), NodeView.KindColor(NodeKind.Card)),
            };
            items.AddRange(SelectionItems());
            if (selectionActions.Any(a => a.Text.Contains("で置く")))
                items.Add(MenuEntry.Item($"置く向きを{(placeUp ? "裏側" : "表側")}にする", () => { placeUp = !placeUp; Render(); },
                    hint: $"今は{(placeUp ? "表側" : "裏側")}で置きます"));
            items.Add(MenuEntry.Separator());
            items.AddRange(CardInfo(c));
            return items;
        }

        // ---- 場のカード ----

        /// <summary>
        /// p のフィールドの i 番目の右クリックのメニュー：そのカードを選び、右の欄と同じ動きを出す。
        /// 対象を選んでいる途中なら「このカードを対象にする」、ブロックを選ぶ場面なら割り当て、スタックの一番上なら解決も出す
        /// </summary>
        public List<MenuEntry> FieldMenu(bool p, int i)
        {
            SelectField(p, i);
            var sl = state.Get(p).Field[i];
            var neg = NegationStatus(out _);
            neg.TryGetValue((p, i), out var status);
            var items = new List<MenuEntry>
            {
                MenuEntry.Title(sl.Card.Name, $"{Who(p)}のフィールド・{sl.Card.Type}" + (sl.FaceUp ? "" : "・裏側") +
                    (UsesMana && TappedAt(p, i) ? "・タップ中" : "") + (status != null ? $"・{status}" : ""), NodeView.KindColor(NodeKind.Card)),
            };
            var situational = new List<MenuEntry>();
            situational.AddRange(TargetItems(p, i, neg));
            situational.AddRange(BlockItems(p, i));
            situational.AddRange(StackItems(sl));
            items.AddRange(situational);
            // 対象・ブロック・スタックの項目があるときは、「できる動きはありません」は出さない
            if (selectionActions.Count > 0 || situational.Count == 0)
            {
                items.AddRange(SelectionItems());
                items.Add(MenuEntry.Separator());
            }
            items.AddRange(SlotInfo(p, i, sl, neg));
            // 場のカードは今の攻守を上に出したので、元の値は重ねて出さない
            items.AddRange(CardInfo(sl.Card, stats: !MatchState.Fights(game.Rules, sl)).Skip(1));
            return items;
        }

        /// <summary>場のカードの今の状態（攻守の今の値・ダメージ・召喚酔い）</summary>
        List<MenuEntry> SlotInfo(bool p, int i, Slot sl, Dictionary<(bool, int), string> neg)
        {
            var items = new List<MenuEntry> { MenuEntry.Header("詳細") };
            if (MatchState.Fights(game.Rules, sl))
            {
                var negs = NegList(neg);
                var atk = state.AtkOf(game.Rules, negs, (p, i), sl);
                var def = state.DefOf(game.Rules, negs, (p, i), sl);
                items.Add(MenuEntry.Info($"今の攻撃力 {atk}・守備力 {def}",
                    atk != sl.Card.Attack || def != sl.Card.Defense ? $"元は {sl.Card.Attack}/{sl.Card.Defense}（永続効果・ターンの終わりまでの変化）" : null));
                if (sl.Damage > 0) items.Add(MenuEntry.Info($"ダメージ {sl.Damage}（あと {Math.Max(0, def - sl.Damage)} で破壊）", "ターンの終わりに消えます"));
                if (p == turn && UsesMana && match.Turn.Sick(game.Rules, state.Get(p).Field, sl))
                    items.Add(MenuEntry.Info("召喚酔い", "置いたターンは攻撃もタップもできません"));
            }
            return items;
        }

        /// <summary>対象を選んでいる途中で、このカードが対象に選べるなら「このカードを対象にする」</summary>
        List<MenuEntry> TargetItems(bool p, int i, Dictionary<(bool, int), string> neg)
        {
            var items = new List<MenuEntry>();
            if (!(targeting is (bool tp, int tk, int te, string message))) return items;
            var f = state.Get(tp).Field;
            if (tk >= f.Count || !(f[tk].Card.Effects[te] is Activated act)) return items;
            if (!TargetsFor(tp, tk, act).Contains((p, i))) return items;
            var name = state.Get(p).Field[i].Card.Name;
            items.Add(MenuEntry.Header($"対象を選ぶ（{f[tk].Card.Name}）"));
            items.Add(MenuEntry.Item("このカードを対象にする",
                () => Do(TChoice.Resolve(tp, tk, te, true, NegList(neg), (p, i)), $"{message}：対象は{Who(p)}の{name}"),
                hint: string.Join(" → ", act.Actions.Select(ActionText))));
            items.Add(MenuEntry.Separator());
            return items;
        }

        /// <summary>ブロックを選ぶ場面で、守る側の戦闘できるカードなら、止める攻撃の割り当て</summary>
        List<MenuEntry> BlockItems(bool p, int j)
        {
            var items = new List<MenuEntry>();
            if (match.Turn.Attackers.Count == 0 || p == turn) return items;
            var of = state.Get(p).Field;
            var tl = of[j];
            if (!MatchState.Fights(game.Rules, tl)) return items;
            var mine = state.Get(turn).Field;
            var atk = TurnInfo.Locate(mine, match.Turn.Attackers);
            items.Add(MenuEntry.Header("ブロック"));
            var ok = Enumerable.Range(0, atk.Count).Where(a => match.Turn.BlockOK(game.Rules, of, new List<(int, int)> { (j, a) })).ToList();
            if (ok.Count == 0)
                items.Add(MenuEntry.Info("このカードはブロックできません", match.Turn.IsTapped(p, of, tl) ? "タップしています"
                    : "このターンにもうブロックしたか、飛行を持つ攻撃です"));
            var has = blockPlan.TryGetValue(j, out var cur);
            items.Add(MenuEntry.Item((has ? "" : "✓ ") + "ブロックしない", () => { blockPlan.Remove(j); Render(); }, ok.Count > 0));
            foreach (var a in ok)
            {
                var aa = a;
                items.Add(MenuEntry.Item((has && cur == a ? "✓ " : "") + $"攻撃 {a + 1}（{mine[atk[a]].Card.Name}）を止める",
                    () => { blockPlan[j] = aa; Render(); }));
            }
            var fight = panelActions.FirstOrDefault(x => x.Text.EndsWith("で戦闘する"));
            if (fight != null) items.Add(MenuEntry.Item(fight.Text, fight.Action, hint: "割り当てたブロックで戦闘のダメージを与えます"));
            items.Add(MenuEntry.Separator());
            return items;
        }

        /// <summary>スタックの一番上のカードなら、右の欄と同じ解決の動き</summary>
        List<MenuEntry> StackItems(Slot sl)
        {
            var items = new List<MenuEntry>();
            var st = match.Turn.Stack;
            if (st.Count == 0 || !TurnInfo.SameSlot(st[0].Item2, sl)) return items;
            items.Add(MenuEntry.Header("スタックの一番上"));
            var acts = panelActions.Where(x => x.Text.StartsWith("一番上")).ToList();
            if (acts.Count > 0) items.AddRange(acts);
            else items.Add(MenuEntry.Info("両者が続けてパスすると解決できます"));
            items.Add(MenuEntry.Separator());
            return items;
        }

        List<MenuEntry> SelectionItems()
        {
            var items = new List<MenuEntry> { MenuEntry.Header("できる動き") };
            if (selectionActions.Count > 0) items.AddRange(selectionActions);
            else items.Add(MenuEntry.Item("今このカードでできる動きはありません", null, false, "理由は右の欄に出ています"));
            return items;
        }

        // ---- 空きのマス ----

        /// <summary>p の手札の h 番目を、ゾーン zi の cell 番目のマスに置く動き（自動の払い方）</summary>
        TChoice PlaceAt(bool p, int h, int zi, int cell, bool up)
        {
            var pay = TurnInfo.AutoPay(state.Get(p).Hand[h], PoolOf(p)) ?? new List<string>();
            return p == turn ? TChoice.Place(h, zi, cell, up, pay) : TChoice.Cast(h, zi, cell, up, pay);
        }

        /// <summary>p のゾーン zi の cell 番目の空きのマスの右クリックのメニュー：そこに置ける手札</summary>
        public List<MenuEntry> CellMenu(bool p, int zi, int cell)
        {
            var items = new List<MenuEntry> { MenuEntry.Title(CellName(zi, cell), $"{Who(p)}の側・空きのマス") };
            var hand = state.Get(p).Hand;
            var any = false;
            var dir = placeUp ? "表側" : "裏側";
            items.Add(MenuEntry.Header($"{Who(p)}の手札から{dir}で置く"));
            var seen = new HashSet<string>();
            for (int h = 0; h < hand.Count; h++)
            {
                var c = hand[h];
                // 同じカードが何枚あっても1つだけ出す
                if (!seen.Add(c.Name)) continue;
                var ch = PlaceAt(p, h, zi, cell, placeUp);
                if (match.Step(game.Rules, ch) == null) continue;
                var pay = ch.Pay;
                var n = hand.Count(x => x.Name == c.Name);
                items.Add(MenuEntry.Item($"{c.Name}を置く",
                    () => Do(ch, $"{Who(p)}：{c.Name} を{CellName(zi, cell)}に{dir}で置く{PayText(pay)}" +
                                 (p != turn ? "（相手のターンにインスタントとして）" : "")),
                    hint: c.Type + (n > 1 ? $"・手札に {n} 枚" : "") +
                          (UsesMana && (c.Cost > 0 || c.ColorCost.Count > 0) ? $"・コスト {CostText(c)}{PayText(pay)}" : ""),
                    swatch: NodeView.KindColor(NodeKind.Card)));
                any = true;
            }
            items.Add(MenuEntry.Separator());
            items.Add(MenuEntry.Item($"置く向きを{(placeUp ? "裏側" : "表側")}にする", () => { placeUp = !placeUp; Render(); },
                hint: $"今は{dir}で置きます"));
            if (!any)
                items.Add(MenuEntry.Item("ここに置ける手札はありません", null, false,
                    p != turn ? $"{Who(turn)}のターンです（{Who(p)}が置けるのはいつでも置けるカードだけ）" : "置ける種類・マナ・1ターンの上限を確かめてください"));
            return items;
        }

        // ---- プレイヤーの盤面 ----

        /// <summary>プレイヤー p の盤面の空き場所の右クリックのメニュー：ライフ・デッキ・手札・墓地と、そのプレイヤーの操作</summary>
        public List<MenuEntry> PlayerMenu(bool p)
        {
            var s = state.Get(p);
            var t = match.Turn;
            var items = new List<MenuEntry>
            {
                MenuEntry.Title(Who(p), (p == turn ? "ターン中" : "相手のターン") + (t.Prio == p ? "・優先権あり" : "")),
                MenuEntry.Info((game.Rules.Life > 0 ? $"ライフ {s.Life}・" : "") + $"デッキ {s.Deck.Count} 枚・手札 {s.Hand.Count} 枚・墓地 {s.Grave.Count} 枚"),
            };
            if (UsesMana) items.Add(MenuEntry.Info($"マナ：{PoolText(PoolOf(p))}"));
            if (t.Prio == p && t.Passes < 2 && !match.Over(game.Rules))
                items.Add(MenuEntry.Item($"{Who(p)}がパスする", () => Do(TChoice.Pass(), $"{Who(p)}：パス"), hint: $"優先権が{Who(!p)}に移ります"));
            if (p == turn)
            {
                var blocked = EndTurnBlocked();
                items.Add(MenuEntry.Item("ターン終了", () => { EndTurn(); Render(); }, blocked == null, blocked));
            }
            items.Add(MenuEntry.Separator());
            items.Add(MenuEntry.Header($"手札（{s.Hand.Count} 枚）"));
            for (int h = 0; h < s.Hand.Count; h++)
            {
                var hh = h;
                items.Add(MenuEntry.Item($"選ぶ：{s.Hand[h].Name}", () => SelectHand(p, hh),
                    hint: CanPlaceNow(p, h) ? "置ける" : null, swatch: NodeView.KindColor(NodeKind.Card)));
            }
            if (s.Hand.Count == 0) items.Add(MenuEntry.Info("なし"));
            items.Add(MenuEntry.Header($"墓地（新しい順・{s.Grave.Count} 枚）"));
            foreach (var g in Enumerable.Reverse(s.Grave).Take(12)) items.Add(MenuEntry.Info(g.Name, g.Type));
            if (s.Grave.Count > 12) items.Add(MenuEntry.Info($"ほか {s.Grave.Count - 12} 枚"));
            if (s.Grave.Count == 0) items.Add(MenuEntry.Info("なし"));
            return items;
        }

        // ---- 空き場所 ----

        /// <summary>MTG 風の見本のカードがそろっていて、動作確認の場面を作れるか</summary>
        bool CanMakeScenarios
        {
            get
            {
                var names = new HashSet<string>(game.Cards.Select(c => c.Name));
                return new[] { "山", "森", "丘巨人", "ゴブリンの先兵", "灰色熊", "紅蓮地獄", "稲妻", "カープルーザンの森", "ショック", "風のドレイク" }
                    .All(names.Contains);
            }
        }

        /// <summary>盤面・右の欄の空き場所の右クリックのメニュー：今できる動き（対象・スタック・ブロックなど）と、対戦の操作</summary>
        public List<MenuEntry> GeneralMenu()
        {
            var items = new List<MenuEntry>();
            if (game == null) return items;
            var t = match.Turn;
            items.Add(MenuEntry.Title($"第{turnCount}ターン：{Who(turn)}のターン", $"優先権：{Who(t.Prio)}" +
                (t.Stack.Count > 0 ? $"・スタック {t.Stack.Count} 枚" : "") + (t.Attackers.Count > 0 ? "・攻撃の途中" : "")));
            if (panelActions.Count > 0)
            {
                items.Add(MenuEntry.Header("今できること"));
                items.AddRange(panelActions);
                items.Add(MenuEntry.Separator());
            }
            items.Add(MenuEntry.Header("対戦"));
            var canPass = t.Passes < 2 && !match.Over(game.Rules) && t.Pending.Count == 0;
            if (canPass)
                items.Add(MenuEntry.Item($"{Who(t.Prio)}がパスする", () => Do(TChoice.Pass(), $"{Who(match.Turn.Prio)}：パス"),
                    hint: $"優先権が{Who(!t.Prio)}に移ります"));
            items.Add(MenuEntry.Item("両者がパスする", () => { PassBoth(); Render(); }, canPass,
                canPass ? (t.Stack.Count > 0 ? "スタックの一番上を解決できるようになります" : t.Attackers.Count > 0 ? "ブロックに進みます" : "何も起きずにターンプレイヤーに戻ります")
                        : "今はパスできません"));
            var blocked = EndTurnBlocked();
            items.Add(MenuEntry.Item("ターン終了", () => { EndTurn(); Render(); }, blocked == null,
                blocked ?? $"{Who(!turn)}のターンになり、{Who(!turn)}が引きます"));
            items.Add(MenuEntry.Item("自動で今のターンを進める", () => Demo(1), !match.Over(game.Rules),
                "置けるカードを置き、スタックを解決し、MTG 式の戦闘なら攻撃を宣言します（ターンは終えません）"));
            if (selHand >= 0 || selField >= 0 || targeting != null)
                items.Add(MenuEntry.Item("選択を解除する", () => { targeting = null; ClearSelection(); Render(); }));
            items.Add(MenuEntry.Separator());
            items.Add(MenuEntry.Header("やり直す・ほか"));
            items.Add(MenuEntry.Item("最初から", () => { seed++; Start(game); }, hint: "山札を混ぜ直します"));
            items.Add(MenuEntry.Item($"{Who(!firstPlayer)}の先攻で最初から", () => { firstPlayer = !firstPlayer; Start(game); }));
            if (CanMakeScenarios)
            {
                items.Add(MenuEntry.Item("場面：まとめての攻撃とブロック", () => Scenario("combat"), hint: "MTG 風の見本の動作確認"));
                items.Add(MenuEntry.Item("場面：スタックで応答", () => Scenario("stack"), hint: "紅蓮地獄に稲妻で応答した場面"));
                items.Add(MenuEntry.Item("場面：対象を選ぶ", () => Scenario("target"), hint: "ショックの対象を選ぶ場面"));
            }
            items.Add(MenuEntry.Item("記録をコピーする", () => GUIUtility.systemCopyBuffer = string.Join("\n", log), hint: "クリップボードへ"));
            if (Exit != null) items.Add(MenuEntry.Item("エディタに戻る", Exit));
            return items;
        }
    }
}
