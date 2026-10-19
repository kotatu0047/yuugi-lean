using System;
using System.Collections.Generic;
using System.Linq;
using UnityEngine;
using UnityEngine.UIElements;

namespace CardGen.App
{
    /// <summary>テストプレイの動作確認用のデモと場面、自動テスト用の口</summary>
    public sealed partial class PlayView
    {
        /// <summary>動作確認用：ターンごとに置ける手札を1枚置いてターンを終え、最後に自分のカードを1枚選ぶ</summary>
        public void Demo(int moves)
        {
            for (int m = 0; m < moves; m++)
            {
                if (m > 0) { DiscardDown(); EndTurn(); }
                var p = turn;
                // マナを使うルールなら、マナを出すカード（土地）を先に置き、タップしてから、払えるカードを置けるだけ置く
                bool DemoPlace(Func<Card, bool> which)
                {
                    var s = state.Get(p);
                    for (int h = 0; h < s.Hand.Count; h++)
                    {
                        if (!which(s.Hand[h])) continue;
                        var pay = TurnInfo.AutoPay(s.Hand[h], match.Turn.Pool);
                        if (pay == null) continue;
                        for (int zi = 0; zi < game.Rules.Zones.Count; zi++)
                        {
                            var cell = state.FreeCell(game.Rules, p, zi);
                            var next = match.Step(game.Rules, TChoice.Place(h, zi, cell, true, pay));
                            if (next == null) continue;
                            log.Add($"{Who(p)}：{s.Hand[h].Name} を{CellName(zi, cell)}に表側で置く{PayText(pay)}");
                            match = next;
                            judge.Sync(state, game.Rules, turn);
                            return true;
                        }
                    }
                    return false;
                }
                if (UsesMana)
                {
                    DemoPlace(c => c.Mana > 0);
                    for (int k = 0; k < state.Get(p).Field.Count; k++)
                    {
                        var land = state.Get(p).Field[k].Card;
                        var color = land.ManaChoice.Count > 0 ? land.ManaChoice[0] : "";
                        var tapped = match.Step(game.Rules, TChoice.Tap(k, color));
                        if (tapped == null) continue;
                        log.Add($"{Who(p)}：{land.Name} をタップ（{ManaText(land, color)}）");
                        match = tapped;
                    }
                    while (DemoPlace(c => c.Mana == 0)) { }
                }
                else DemoPlace(c => true);
                // スタックに積んだ呪文は、一番上から解決する
                while (match.Turn.Stack.Count > 0)
                {
                    PassBoth();
                    var (q, top) = match.Turn.Stack[0];
                    var k = state.Get(q).Field.FindIndex(x => TurnInfo.SameSlot(x, top));
                    var e = top.Card.Effects.FindIndex(x => x is Activated);
                    var next = k < 0 || e < 0 ? null : match.Step(game.Rules, TChoice.Resolve(q, k, e, true, new List<(bool, int)>()));
                    if (next == null) break;
                    log.Add($"{Who(q)}：{top.Card.Name} を解決");
                    match = next;
                    judge.Sync(state, game.Rules, turn);
                }
            }
            // MTG 式の戦闘なら、攻撃できるカードをすべて宣言してブロックの場面を見せる
            if (game.Rules.Blocking)
            {
                for (int k = 0; k < state.Get(turn).Field.Count; k++)
                {
                    var next = match.Step(game.Rules, TChoice.Attack(k, null, new List<(bool, int)>()));
                    if (next == null) continue;
                    log.Add($"{Who(turn)}：{state.Get(turn).Field[k].Card.Name} で攻撃（宣言）");
                    match = next;
                }
                if (match.Turn.Attackers.Count > 0) { PassBoth(); Render(); return; }
            }
            var f = state.Get(true).Field;
            selPlayer = true;
            // 攻撃できるカードがあればそれを、なければ発動できるカードを選ぶ
            selField = f.FindIndex(sl => sl.FaceUp && MatchState.Fights(game.Rules, sl));
            if (selField < 0) selField = f.FindIndex(sl => sl.Card.Effects.Any(e => e is Activated));
            Render();
        }

        /// <summary>
        /// 動作確認用の場面（MTG 風の見本のカードを使う）。"combat"：自分がゴブリンの先兵と丘巨人で攻撃を宣言し、
        /// 相手が灰色熊2体で丘巨人をブロックしようとしている。"stack"：自分が紅蓮地獄を唱え、相手が稲妻で応答した。
        /// "target"：自分がショックを唱え、解決するときに対象を選ぶ
        /// </summary>
        public void Scenario(string name)
        {
            var c = game.Cards.GroupBy(x => x.Name).ToDictionary(g => g.Key, g => g.First());
            string[] need = { "山", "森", "丘巨人", "ゴブリンの先兵", "灰色熊", "紅蓮地獄", "稲妻", "カープルーザンの森", "ショック", "風のドレイク" };
            if (need.Any(n => !c.ContainsKey(n))) { log.Add("（場面を作れません：MTG 風の見本のカードがありません）"); Render(); return; }
            PState P(string[] field, string[] hand) => new PState
            {
                Deck = Enumerable.Repeat(c["山"], 20).ToList(),
                Hand = hand.Select(n => c[n]).ToList(),
                Field = field.Select((n, i) => new Slot(0, i, c[n], true)).ToList(),
                Life = game.Rules.Life,
            };
            var none = new List<(bool, int)>();
            if (name == "combat")
            {
                match = new Match
                {
                    G = new MatchState
                    {
                        P1 = P(new[] { "山", "山", "ゴブリンの先兵", "丘巨人" }, new[] { "紅蓮地獄" }),
                        P2 = P(new[] { "森", "カープルーザンの森", "灰色熊", "灰色熊" }, new[] { "稲妻" }),
                    },
                    Turn = new TurnInfo { Tp = true, Count = 5 },
                };
                match = match.Step(game.Rules, TChoice.Attack(2, null, none)) ?? match;
                match = match.Step(game.Rules, TChoice.Attack(3, null, none)) ?? match;
                PassBoth();
                blockPlan[2] = 1;
                blockPlan[3] = 1;
                log.Add("場面：自分がゴブリンの先兵と丘巨人で攻撃を宣言し、相手が灰色熊2体で丘巨人をブロックしようとしている");
            }
            else if (name == "target")
            {
                match = new Match
                {
                    G = new MatchState
                    {
                        P1 = P(new[] { "山", "山", "丘巨人" }, new[] { "ショック" }),
                        P2 = P(new[] { "森", "灰色熊", "ゴブリンの先兵", "風のドレイク" }, new[] { "稲妻" }),
                    },
                    Turn = new TurnInfo { Tp = true, Count = 5 },
                };
                foreach (var ch in new[] { TChoice.Tap(0), TChoice.Place(0, 1, 0, true, new List<string> { "赤" }) })
                    match = match.Step(game.Rules, ch) ?? match;
                PassBoth();
                var k = state.P1.Field.Count - 1;
                targeting = (true, k, 0, "自分：ショック を解決");
                log.Add("場面：自分がショックを唱え、解決するときに対象を選ぶ");
            }
            else
            {
                match = new Match
                {
                    G = new MatchState
                    {
                        P1 = P(new[] { "山", "山", "丘巨人" }, new[] { "紅蓮地獄" }),
                        P2 = P(new[] { "山", "カープルーザンの森", "ゴブリンの先兵" }, new[] { "稲妻" }),
                    },
                    Turn = new TurnInfo { Tp = true, Count = 5 },
                };
                foreach (var ch in new[] { TChoice.Tap(0), TChoice.Tap(1), TChoice.Place(0, 1, 0, true, new List<string> { "赤", "赤" }),
                                           TChoice.Pass(), TChoice.OppTap(0), TChoice.Cast(0, 1, 0, true, new List<string> { "赤" }) })
                    match = match.Step(game.Rules, ch) ?? match;
                log.Add("場面：自分が紅蓮地獄を唱え、相手が応答して稲妻を唱えた（稲妻が一番上）");
            }
            judge = new Judge();
            judge.Sync(state, game.Rules, turn);
            ClearSelection();
            Render();
        }

        // ---- 自動テスト用 ----

        /// <summary>今の対戦（テスト用）</summary>
        public Match CurrentMatch => match;
        /// <summary>記録（古い順。テスト用）</summary>
        public IReadOnlyList<string> Log => log;
        /// <summary>p の手札の i 番目を選ぶ（カードの表示をクリックしたのと同じ）</summary>
        public void SelectHand(bool p, int i) { selPlayer = p; selHand = i; selField = -1; customPay = null; Render(); }
        /// <summary>p のフィールドの i 番目を選ぶ</summary>
        public void SelectField(bool p, int i) { selPlayer = p; selField = i; selHand = -1; customPay = null; Render(); }
        /// <summary>p の手札の i 番目が「置ける」と表示されるか</summary>
        public bool ShowsPlaceable(bool p, int i) => CanPlaceNow(p, i);
    }
}
