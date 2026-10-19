using System;
using System.Collections.Generic;
using System.Linq;
using UnityEngine;
using UnityEngine.UIElements;

namespace CardGen.App
{
    /// <summary>テストプレイの右の欄（優先権・対象・ブロック・スタック・支払い）と画面全体の描き直し</summary>
    public sealed partial class PlayView
    {
        /// <summary>優先権の欄：誰が持っているか、パスの回数、パスするボタン</summary>
        void PriorityPanel()
        {
            var t = match.Turn;
            var row = Row();
            row.style.alignItems = Align.Center;
            row.style.marginTop = 6;
            var what = t.Passes == 2
                ? (t.Stack.Count > 0 ? "両者がパスしました。スタックの一番上を解決します" : "両者がパスしました。ブロックを選びます")
                : t.Passes == 1 ? $"{Who(!t.Prio)}がパスしました。{Who(t.Prio)}もパスすると、" +
                    (t.Stack.Count > 0 ? "一番上を解決します" : t.Attackers.Count > 0 ? "ブロックに進みます" : "何も起きずにターンプレイヤーに戻ります")
                : "優先権を持つプレイヤーだけが動けます（動いても優先権は自分のまま。パスすると相手に移ります）";
            row.Add(Text($"優先権：{Who(t.Prio)}", 14, Good, true));
            if (t.Passes < 2 && !match.Over(game.Rules))
            {
                var b = UiTest.Btn($"{Who(t.Prio)}がパスする", () => Do(TChoice.Pass(), $"{Who(match.Turn.Prio)}：パス"));
                b.style.marginLeft = 12;
                row.Add(b);
            }
            side.Add(row);
            side.Add(Text(what, 11, t.Passes == 2 ? Warn : Quiet));
        }

        /// <summary>対象を選ぶ欄</summary>
        void TargetPanel(Dictionary<(bool, int), string> neg)
        {
            if (!(targeting is (bool p, int k, int e, string message))) return;
            var f = state.Get(p).Field;
            if (k >= f.Count || !(f[k].Card.Effects[e] is Activated act)) { targeting = null; return; }
            Section($"対象を選ぶ（{f[k].Card.Name}）");
            var negs = NegList(neg);
            foreach (var (q, i) in TargetsFor(p, k, act))
            {
                var sl = state.Get(q).Field[i];
                int qi = i;
                bool qq = q;
                ActionButton($"{Who(q)}の{sl.Card.Name}を対象にする",
                    () => Do(TChoice.Resolve(p, k, e, true, negs, (qq, qi)), $"{message}：対象は{Who(qq)}の{sl.Card.Name}"));
            }
            ActionButton("対象を選ばずに解決する（対象を選ぶ動きは何も起きない）", () => Do(TChoice.Resolve(p, k, e, true, negs), message + "（対象なし）"));
            ActionButton("やめる", () => { targeting = null; Render(); });
        }

        /// <summary>MTG 式の戦闘：攻撃されたプレイヤーが、攻撃ごとにブロックするカードを割り当てる（1枚の攻撃に何枚でも）</summary>
        void BlockPanel(Dictionary<(bool, int), string> neg)
        {
            var p = turn;
            var o = !p;
            var negs = NegList(neg);
            var mine = state.Get(p).Field;
            var atk = TurnInfo.Locate(mine, match.Turn.Attackers);
            Section($"ブロック（{Who(o)}が選ぶ）");
            for (int a = 0; a < atk.Count; a++)
            {
                var sl = mine[atk[a]];
                side.Add(Text($"攻撃 {a + 1}：{Who(p)}の{sl.Card.Name}（{state.AtkOf(game.Rules, negs, (p, atk[a]), sl)}/" +
                              $"{state.DefOf(game.Rules, negs, (p, atk[a]), sl)}{(sl.Damage > 0 ? $"・ダメージ {sl.Damage}" : "")}）", 12, Warn, true));
            }
            if (game.Rules.Stack && match.Turn.Stack.Count > 0)
                side.Add(Text("スタックにカードがあります。ブロックはスタックが空になってから選べます（その前にインスタントで応答できます）", 11, Warn));
            if (game.Rules.Instants.Count > 0)
                side.Add(Text($"ブロックを選ぶ前に、どちらのプレイヤーもインスタントを置けます（手札のインスタントを選んでください）", 11, Quiet));
            var of = state.Get(o).Field;
            for (int j = 0; j < of.Count; j++)
            {
                var tl = of[j];
                if (!MatchState.Fights(game.Rules, tl)) continue;
                var row = Row();
                row.style.alignItems = Align.Center;
                row.style.marginTop = 4;
                var name = Text($"{tl.Card.Name}（{state.AtkOf(game.Rules, negs, (o, j), tl)}/{state.DefOf(game.Rules, negs, (o, j), tl)}）", 11, Color.white);
                name.style.width = 150;
                row.Add(name);
                int jj = j;
                if (!Enumerable.Range(0, atk.Count).Any(a => match.Turn.BlockOK(game.Rules, of, new List<(int, int)> { (jj, a) })))
                {
                    row.Add(Text(match.Turn.IsTapped(o, of, tl) ? "タップしているのでブロックできません"
                        : match.Turn.Blocked.Any(x => TurnInfo.SameSlot(x, tl)) ? "このターンにもうブロックしました"
                        : "飛行を持つ攻撃は、飛行か到達を持つカードでしかブロックできません", 11, Quiet));
                    side.Add(row);
                    continue;
                }
                blockPlan.TryGetValue(jj, out var cur);
                var has = blockPlan.ContainsKey(jj);
                void Opt(string label, int? a)
                {
                    var on = a == null ? !has : has && cur == a.Value;
                    var b = UiTest.Btn(label, () => { if (a == null) blockPlan.Remove(jj); else blockPlan[jj] = a.Value; Render(); });
                    b.style.backgroundColor = on ? new Color(0.28f, 0.45f, 0.62f) : new Color(0.22f, 0.22f, 0.25f);
                    row.Add(b);
                }
                Opt("ブロックしない", null);
                for (int a = 0; a < atk.Count; a++)
                    if (match.Turn.BlockOK(game.Rules, of, new List<(int, int)> { (jj, a) })) Opt($"攻撃 {a + 1} を止める", a);
                side.Add(row);
            }
            // 割り当てたブロックで戦闘したときの結果（C# の対戦エンジンで計算した予告）
            var blocks = blockPlan.OrderBy(kv => kv.Key).Select(kv => (kv.Key, kv.Value)).ToList();
            var after = state.Combat(game.Rules, negs, p, atk, blocks);
            var notes = new List<string>();
            foreach (var q in new[] { p, o })
            {
                var before = state.Get(q).Field;
                var gone = before.Where(x => !after.Get(q).Field.Any(y => y.Key == x.Key)).Select(x => x.Card.Name).ToList();
                if (gone.Count > 0) notes.Add($"{Who(q)}の{string.Join("・", gone)}が破壊される");
                foreach (var y in after.Get(q).Field)
                {
                    var x = before.FirstOrDefault(z => z.Key == y.Key);
                    if (x != null && y.Damage > x.Damage) notes.Add($"{Who(q)}の{y.Card.Name}は {y.Damage - x.Damage} のダメージを受けて残る");
                }
                var lost = state.Get(q).Life - after.Get(q).Life;
                if (lost > 0) notes.Add($"{Who(q)}に {lost} ダメージ");
            }
            side.Add(Text("結果の予告：" + (notes.Count == 0 ? "何も起きない" : string.Join("、", notes)), 12, Good));
            if (match.Turn.Passes < 2)
            {
                side.Add(Text("両者が続けてパスすると、このブロックで戦闘できます（その前にインスタントで応答できます）", 11, Quiet));
                return;
            }
            ActionButton(blocks.Count == 0 ? "ブロックしないで戦闘する" : "このブロックで戦闘する",
                () => Do(TChoice.Block(blocks, negs), $"{Who(o)}：" +
                    (blocks.Count == 0 ? "ブロックしない" : string.Join("、", blocks.Select(b => $"{of[b.Item1].Card.Name}で攻撃 {b.Item2 + 1} をブロック"))) +
                    $"（{(notes.Count == 0 ? "何も起きない" : string.Join("、", notes))}）"));
        }

        /// <summary>スタック（一番上から）。一番上だけ解決できる</summary>
        void StackPanel(Dictionary<(bool, int), string> neg)
        {
            var st = match.Turn.Stack;
            if (!game.Rules.Stack || st.Count == 0) return;
            Section("スタック（上から順に解決）");
            for (int i = 0; i < st.Count; i++)
            {
                var (q, sl) = st[i];
                side.Add(Text($"{i + 1}. {Who(q)}の{sl.Card.Name}" + (i == 0 ? "（一番上）" : ""), 12, i == 0 ? Warn : Quiet, i == 0));
            }
            var (tq, top) = st[0];
            var k = state.Get(tq).Field.FindIndex(x => TurnInfo.SameSlot(x, top));
            if (k < 0) return;
            if (match.Turn.Passes < 2)
            {
                side.Add(Text("両者が続けてパスすると、一番上を解決します（その前に、優先権を持つプレイヤーはインスタントで応答できます）", 11, Quiet));
                return;
            }
            neg.TryGetValue((tq, k), out var status);
            for (int e = 0; e < top.Card.Effects.Count; e++)
            {
                if (!(top.Card.Effects[e] is Activated act)) continue;
                var what = string.Join("、", act.Actions.Select(ActionText));
                int ei = e;
                if (status != "無効")
                    ActionButton($"一番上を解決する：{top.Card.Name}（{what}）",
                        () => StartResolve(tq, k, ei, true, NegList(neg), $"{Who(tq)}：{top.Card.Name} を解決（{what}）"));
                if (status != "有効")
                    ActionButton($"一番上を、無効にされた状態で解決する（{top.Card.Name}。何も起きない）",
                        () => Do(TChoice.Resolve(tq, k, ei, false, NegList(neg)), $"{Who(tq)}：{top.Card.Name} を解決したが無効"));
            }
            side.Add(Text("解決する前に、どちらのプレイヤーもインスタントで応答できます（後に置いたものから解決）", 11, Quiet));
        }

        /// <summary>手札を置くときに払うマナを選ぶ欄</summary>
        void PayPanel(bool p, Card c)
        {
            if (!UsesMana || (c.Cost == 0 && c.ColorCost.Count == 0)) return;
            var pool = PoolOf(p);
            var pay = SelectedPay(p);
            var ok = TurnInfo.PayOK(c, pool, pay);
            side.Add(Text($"コスト {CostText(c)}・{Who(p)}のマナ {PoolText(pool)}", 12, Quiet));
            side.Add(Text($"払うマナ：{(pay.Count == 0 ? "なし" : PoolText(pay))}" + (customPay == null ? "（自動の払い方）" : "（自分で選んだ払い方）") +
                          (ok ? "" : "　→ これでは払えません"), 12, ok ? Good : Warn));
            var row = Row();
            row.style.alignItems = Align.Center;
            foreach (var col in pool.Distinct())
            {
                var cc = col;
                var used = (customPay ?? new List<string>()).Count(x => x == cc);
                if (used >= pool.Count(x => x == cc)) continue;
                row.Add(UiTest.Btn($"＋{ColorName(cc)}", () => { customPay = (customPay ?? new List<string>()).Append(cc).ToList(); Render(); }));
            }
            row.Add(UiTest.Btn("選び直す", () => { customPay = new List<string>(); Render(); }));
            if (customPay != null) row.Add(UiTest.Btn("自動の払い方に戻す", () => { customPay = null; Render(); }));
            side.Add(row);
        }

        void Section(string title)
        {
            var l = Text(title, 14, Color.white, true);
            l.style.marginTop = 12;
            l.style.marginBottom = 4;
            side.Add(l);
        }

        void ActionButton(string text, System.Action a)
        {
            var b = UiTest.Btn(text, a);
            b.style.marginTop = 4;
            b.style.whiteSpace = WhiteSpace.Normal;
            side.Add(b);
        }

        void Render()
        {
            if (game == null) return;
            var neg = NegationStatus(out var negSummary);
            boards.Clear();
            boards.Add(PlayerBoard(false, neg));
            boards.Add(GridBoard(neg));
            boards.Add(PlayerBoard(true, neg));

            side.Clear();
            var top = Row();
            top.style.alignItems = Align.Center;
            top.Add(Text("テストプレイ", 16, Color.white, true));
            var restart = UiTest.Btn("最初から（混ぜ直す）", () => { seed++; Start(game); });
            restart.style.marginLeft = 12;
            top.Add(restart);
            side.Add(top);
            var turnRow = Row();
            turnRow.style.alignItems = Align.Center;
            turnRow.style.marginTop = 6;
            turnRow.Add(Text($"第{turnCount}ターン：{Who(turn)}のターン", 14, Warn, true));
            var endTurn = UiTest.Btn("ターン終了", () => { EndTurn(); Render(); });
            endTurn.style.marginLeft = 12;
            endTurn.SetEnabled(match.Turn.Quiet && !match.Over(game.Rules) && match.Turn.Prio == turn && match.Turn.Passes < 2);
            turnRow.Add(endTurn);
            var swap = UiTest.Btn($"{Who(!firstPlayer)}の先攻で最初から", () => { firstPlayer = !firstPlayer; Start(game); });
            swap.style.marginLeft = 6;
            turnRow.Add(swap);
            side.Add(turnRow);
            var lim = game.Rules.SummonsPerTurn == 0 ? "制限なし" : $"{match.Turn.Summons}/{game.Rules.SummonsPerTurn}";
            side.Add(Text($"このターンの召喚：{lim}・攻撃したカード：{match.Turn.Attacked.Count} 枚", 11, Quiet));
            if (UsesMana)
                side.Add(Text($"{Who(turn)}のマナ：{PoolText(match.Turn.Pool)}" +
                              (game.Rules.Instants.Count > 0 ? $"・{Who(!turn)}のマナ：{PoolText(match.Turn.OppPool)}" : "") +
                              "（ターンの終わりに消えます）", 13, Good, true));
            if (UsesMana && (match.Turn.Made > 0 || match.Turn.Spent > 0))
                side.Add(Text($"このターンにタップで出したマナ {match.Turn.Made}・払ったマナ {match.Turn.Spent}（払うマナは出したマナを超えない：Lean で証明済み）", 11, Quiet));
            if (game.Rules.PlaceLimits.Count > 0)
                side.Add(Text("このターンに置いた枚数：" + string.Join("・", game.Rules.PlaceLimits.Select(l =>
                    $"{string.Join("+", l.Types)} {match.Turn.Placed.Count(l.Types.Contains)}/{l.Count}")), 11, Quiet));
            side.Add(Text("両方のプレイヤーを動かせます。動けるのは優先権を持つプレイヤーだけです（公理）。カードを置く・攻撃するのは" +
                          "ターンプレイヤーだけで（インスタントはどちらも置けます）、場のカードの発動はどちらのターンでもできます。" +
                          "相手に動いてほしいときは「パスする」で優先権を渡します。引くのはターンの最初だけです。カードを選ぶと、できる動きが出ます。", 11, Quiet));
            PriorityPanel();
            var winner = Winner();
            if (winner != null)
            {
                Section("勝敗");
                side.Add(Text(winner + "。対戦は終わりました（「最初から」でやり直せます）", 14, Warn, true));
            }
            if (judge.Choices != null)
                side.Add(Text("無効の判定で、プレイヤーが選ぶ場面です（下の「無効の状態」から選んでください）", 12, Warn, true));
            TargetPanel(neg);
            StackPanel(neg);
            if (match.Turn.Attackers.Count > 0)
                BlockPanel(neg);

            Section("選んでいるカード");
            var s = state.Get(selPlayer);
            if (selHand >= 0 && selHand < s.Hand.Count)
            {
                var c = s.Hand[selHand];
                side.Add(Text($"{Who(selPlayer)}の手札：{c.Name}（{c.Type}）", 12, Color.white));
                bool any = false;
                if (selPlayer != turn && !TurnInfo.Instant(game.Rules, c))
                {
                    side.Add(Text($"{Who(turn)}のターンなので、{Who(selPlayer)}は手札を置けません" +
                                  (game.Rules.Instants.Count > 0 ? $"（いつでも置けるのは {string.Join("・", game.Rules.Instants)} だけ）" : ""), 12, Warn));
                    any = true;
                }
                else
                {
                    if (selPlayer != turn)
                        side.Add(Text($"いつでも置けるカード（{c.Type}）なので、{Who(turn)}のターンでも置けます（{Who(selPlayer)}のカードをタップして出したマナで払う）", 11, Quiet));
                    PayPanel(selPlayer, c);
                    var upRow = Row();
                    upRow.style.alignItems = Align.Center;
                    upRow.Add(Text("置く向き：", 12, Quiet));
                    foreach (var up in new[] { true, false })
                    {
                        var u = up;
                        var b = UiTest.Btn((up ? "表側" : "裏側") + (placeUp == up ? "（選択中）" : ""), () => { placeUp = u; Render(); });
                        upRow.Add(b);
                    }
                    side.Add(upRow);
                    for (int zi = 0; zi < game.Rules.Zones.Count; zi++)
                    {
                        var z = game.Rules.Zones[zi];
                        var free = Enumerable.Range(0, z.Count).Where(k => CanPlaceSelected(selPlayer, zi, k)).ToList();
                        if (free.Count == 0)
                        {
                            // 置ける場所なのに、召喚の上限・種類ごとの上限・マナで置けないときは、そう伝える
                            var cell = state.FreeCell(game.Rules, selPlayer, zi);
                            var why = selPlayer == turn ? PlaceBlocked(new Slot(zi, cell, c, placeUp))
                                : TurnInfo.AutoPay(c, match.Turn.OppPool) == null
                                    ? $"マナが足りません（コスト {CostText(c)}・{Who(selPlayer)}のマナ {PoolText(match.Turn.OppPool)}）。{Who(selPlayer)}のマナを出すカードを選んでタップしてください"
                                    : "選んだマナでは払えません";
                            if (state.Step(game.Rules, Choice.Place(selPlayer, selHand, zi, cell, placeUp)) != null && !any && why != null)
                            {
                                side.Add(Text(why, 12, Warn));
                                any = true;
                            }
                            continue;
                        }
                        any = true;
                        int zz = zi;
                        int first = free[0];
                        var where = z.Capacity == Capacity.One && z.Count > 1
                            ? $"（空いているマス：{string.Join("・", free.Select(k => k + 1))}。{first + 1}番目に置く）" : "";
                        ActionButton($"{z.Name}に{(placeUp ? "表側" : "裏側")}で置く{where}", () => PlaceSelected(zz, first));
                    }
                    if (any) side.Add(Text("フィールドの「ここに置く」のマスをクリックしても置けます", 11, Quiet));
                }
                if (!any) side.Add(Text("置けるゾーンがありません", 12, Warn));
            }
            else if (selField >= 0 && selField < s.Field.Count)
            {
                var sl = s.Field[selField];
                side.Add(Text($"{Who(selPlayer)}のフィールド：{sl.Card.Name}（{sl.Card.Type}・{(sl.FaceUp ? "表側" : "裏側")}）", 12, Color.white));
                neg.TryGetValue((selPlayer, selField), out var st);
                if (st != null) side.Add(Text($"効果の状態：{st}", 12, st == "有効" ? Good : st == "無効" ? Bad : Warn));
                var hasAct = sl.Card.Effects.Any(e => e is Activated);
                if (hasAct && !match.Turn.TopOK(game.Rules, state, selPlayer, selField))
                    side.Add(Text("スタックの一番上のカードから解決します（右の「スタック」の欄）", 12, Warn));
                else
                    for (int e = 0; e < sl.Card.Effects.Count; e++)
                    {
                        if (!(sl.Card.Effects[e] is Activated act)) continue;
                        var what = string.Join("、", act.Actions.Select(ActionText));
                        int ei = e;
                        var negs = NegList(neg);
                        if (st != "無効")
                            ActionButton($"発動する（{what}）", () => StartResolve(selPlayer, selField, ei, true, negs, $"{Who(selPlayer)}：{sl.Card.Name} を発動（{what}）"));
                        if (st != "有効")
                            ActionButton("無効にされた状態で解決する（何も起きない）", () => Do(TChoice.Resolve(selPlayer, selField, ei, false, negs), $"{Who(selPlayer)}：{sl.Card.Name} を発動したが無効"));
                    }
                if (sl.Card.Mana > 0)
                {
                    var mine = selPlayer == turn;
                    var canTap = mine ? match.Turn.TapOK(game.Rules, s.Field, sl) : match.Turn.OppTapOK(game.Rules, s.Field, sl);
                    if (!mine && game.Rules.Instants.Count == 0)
                        side.Add(Text($"{Who(turn)}のターンなので、タップしてマナを出せません", 12, Quiet));
                    else if (canTap)
                    {
                        int tk = selField;
                        bool pp = selPlayer;
                        var colors = sl.Card.ManaChoice.Count > 0 ? sl.Card.ManaChoice : new List<string> { "" };
                        foreach (var col in colors)
                        {
                            var cc = col;
                            var label = ManaText(sl.Card, sl.Card.ManaChoice.Count > 0 ? cc : null);
                            ActionButton($"タップしてマナを出す（{label}）" + (mine ? "" : $"：{Who(pp)}のインスタント用"),
                                () => Do(mine ? TChoice.Tap(tk, cc) : TChoice.OppTap(tk, cc), $"{Who(pp)}：{sl.Card.Name} をタップ（{label}）"));
                        }
                    }
                    else if (match.Turn.IsTapped(selPlayer, s.Field, sl))
                        side.Add(Text("タップしています（次の自分のターンの始めに起きます）", 12, Quiet));
                    else if (match.Turn.Sick(game.Rules, s.Field, sl))
                        side.Add(Text("召喚酔いで、このターンはタップできません", 12, Quiet));
                    else if (!sl.FaceUp)
                        side.Add(Text("裏側のカードはタップしてマナを出せません", 12, Quiet));
                }
                foreach (var n in sl.Card.Effects.OfType<Negate>())
                    side.Add(Text($"永続効果：{NodeView.SelectorSummary(n.Target).Replace("\n", "・")}の効果を無効にする", 11, Quiet));
                foreach (var bo in sl.Card.Effects.OfType<Boost>())
                    side.Add(Text($"永続効果：{NodeView.SelectorSummary(bo.Target).Replace("\n", "・")}の攻撃力を{(bo.Amount >= 0 ? "+" : "")}{bo.Amount}", 11, Quiet));
                foreach (var tg in sl.Card.Effects.OfType<Toughen>())
                    side.Add(Text($"永続効果：{NodeView.SelectorSummary(tg.Target).Replace("\n", "・")}の守備力を{(tg.Amount >= 0 ? "+" : "")}{tg.Amount}", 11, Quiet));
                if (sl.Damage > 0)
                    side.Add(Text($"受けているダメージ：{sl.Damage}（ターンの終わりに消えます）", 12, Bad));
                if (sl.FaceUp && MatchState.Fights(game.Rules, sl) && selPlayer != turn)
                    side.Add(Text($"{Who(turn)}のターンなので攻撃できません", 12, Quiet));
                else if (sl.FaceUp && MatchState.Fights(game.Rules, sl) && match.Turn.Stack.Count > 0)
                    side.Add(Text("スタックにカードがあるので、空になるまで攻撃できません", 12, Quiet));
                else if (sl.FaceUp && MatchState.Fights(game.Rules, sl) && !match.AttackPhaseOK(game.Rules))
                    side.Add(Text("先攻の最初のターンは攻撃できません", 12, Quiet));
                else if (sl.FaceUp && MatchState.Fights(game.Rules, sl) && !match.Turn.CanAttack(sl, s.Field))
                    side.Add(Text("このカードはこのターンにもう攻撃しました", 12, Quiet));
                else if (sl.FaceUp && MatchState.Fights(game.Rules, sl) && game.Rules.AttackTaps && match.Turn.IsTapped(selPlayer, s.Field, sl))
                    side.Add(Text("タップしているので攻撃できません", 12, Quiet));
                else if (sl.FaceUp && MatchState.Fights(game.Rules, sl) && match.Turn.Sick(game.Rules, s.Field, sl))
                    side.Add(Text("召喚酔いで、置いたターンには攻撃できません", 12, Quiet));
                else if (sl.FaceUp && MatchState.Fights(game.Rules, sl))
                {
                    var negs = NegList(neg);
                    var a = state.AtkOf(game.Rules, negs, (selPlayer, selField), sl);
                    var o = !selPlayer;
                    var of = state.Get(o).Field;
                    int pk = selField;
                    bool pp = selPlayer;
                    if (game.Rules.Blocking)
                    {
                        ActionButton($"攻撃を宣言する（攻撃力 {a}。ほかのカードも宣言してから、{Who(o)}がブロックを選ぶ）",
                            () => Do(TChoice.Attack(pk, null, negs), $"{Who(pp)}：{sl.Card.Name}（{a}）で攻撃（宣言）"));
                        of = new List<Slot>();
                    }
                    for (int j = 0; j < of.Count; j++)
                    {
                        if (!state.TargetOK(game.Rules, pp, j)) continue;
                        var tl = of[j];
                        var vs = tl.FaceUp ? $"攻撃力 {state.AtkOf(game.Rules, negs, (o, j), tl)}" : $"裏側・守備力 {state.DefOf(game.Rules, negs, (o, j), tl)}";
                        var name = tl.FaceUp ? tl.Card.Name : "裏側のカード";
                        int tj = j;
                        ActionButton($"{name}を攻撃する（{a} 対 {vs}）",
                            () => Do(TChoice.Attack(pk, tj, negs), $"{Who(pp)}：{sl.Card.Name}（{a}）で{name}（{vs}）を攻撃"));
                    }
                    if (!game.Rules.Blocking && state.TargetOK(game.Rules, pp, null))
                        ActionButton($"直接攻撃する（{a} ダメージ）", () => Do(TChoice.Attack(pk, null, negs), $"{Who(pp)}：{sl.Card.Name}で直接攻撃（{a}）"));
                }
            }
            else side.Add(Text("（なし）", 12, Quiet));

            Section("無効の状態");
            var ok = judge.Result == Judge.Outcome.Unique || judge.Result == Judge.Outcome.Done;
            side.Add(Text(negSummary, 12, ok ? Good : Warn));
            if (judge.Choices != null)
            {
                side.Add(Text(ChooserText(), 12, Warn));
                for (int k = 0; k < judge.Choices.Count; k++)
                {
                    int kk = k;
                    var t = ChoiceText(judge.Choices[k].card);
                    ActionButton(t, () => Choose(kk, t));
                }
            }
            side.Add(Text($"判定のターンプレイヤー：{Who(judge.Turn)}（同時に適用を始めるカードは、ターンプレイヤーのものが先）", 11, Quiet));

            Section("盤面の制約");
            var v = state.Violations(game.Rules);
            if (v.Count == 0) side.Add(Text("すべて成り立っています（枚数・置けるゾーン・1マス1枚。Lean で証明済み）", 12, Good));
            foreach (var m in v) side.Add(Text("・" + m, 12, Bad));

            Section("記録");
            foreach (var m in Enumerable.Reverse(log).Take(20)) side.Add(Text(m, 11, Quiet));
        }
    }
}
