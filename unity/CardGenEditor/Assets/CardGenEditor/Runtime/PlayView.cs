using System;
using System.Collections.Generic;
using System.Linq;
using UnityEngine;
using UnityEngine.UIElements;

namespace CardGen.App
{
    /// <summary>
    /// テストプレイ：作ったルールとカードで、両プレイヤーを1人で動かす。
    /// 動きは C# の対戦エンジン（Lean の State.step? と差分テスト済み）で進め、
    /// フィールドの無効の状態と、盤面の制約（Lean で証明済み）をその都度表示する。
    /// 攻撃力は、無効の状態が1通りに決まるときはそれを使い、決まらないカードは有効として計算する。
    /// </summary>
    public sealed class PlayView : VisualElement
    {
        Game game;
        MatchState state;
        int seed = 1;
        readonly List<string> log = new List<string>();

        // 選んでいるカード
        bool selPlayer;
        int selHand = -1;
        int selField = -1;

        readonly VisualElement boards;
        readonly VisualElement side;

        static readonly Color Panel = new Color(0.16f, 0.16f, 0.18f);
        static readonly Color Line = new Color(0.3f, 0.3f, 0.33f);
        static readonly Color Good = new Color(0.45f, 0.8f, 0.5f);
        static readonly Color Bad = new Color(0.95f, 0.45f, 0.4f);
        static readonly Color Warn = new Color(0.95f, 0.75f, 0.35f);
        static readonly Color Quiet = new Color(0.7f, 0.7f, 0.75f);

        public PlayView()
        {
            style.flexGrow = 1;
            style.flexDirection = FlexDirection.Row;
            var boardScroll = new ScrollView();
            boardScroll.style.flexGrow = 1;
            boards = new VisualElement();
            boards.style.paddingLeft = 16;
            boards.style.paddingRight = 16;
            boards.style.paddingTop = 8;
            boardScroll.Add(boards);
            Add(boardScroll);
            var sideScroll = new ScrollView();
            sideScroll.style.width = 420;
            sideScroll.style.backgroundColor = Panel;
            sideScroll.style.borderLeftWidth = 1;
            sideScroll.style.borderLeftColor = Line;
            side = new VisualElement();
            side.style.paddingLeft = 12;
            side.style.paddingRight = 12;
            side.style.paddingTop = 10;
            sideScroll.Add(side);
            Add(sideScroll);
        }

        /// <summary>カードの一覧からデッキを作る（デッキの枚数になるまで繰り返し、混ぜる）</summary>
        List<Card> MakeDeck(System.Random rng)
        {
            var d = Enumerable.Range(0, game.Rules.DeckSize).Select(i => game.Cards[i % game.Cards.Count]).ToList();
            for (int i = d.Count - 1; i > 0; i--)
            {
                int j = rng.Next(i + 1);
                (d[i], d[j]) = (d[j], d[i]);
            }
            return d;
        }

        public void Start(Game g)
        {
            game = g;
            var rng = new System.Random(seed);
            state = MatchState.Start(g.Rules, MakeDeck(rng), MakeDeck(rng));
            log.Clear();
            log.Add($"開始（混ぜ方 {seed}）：お互いに {g.Rules.HandSize} 枚引きました");
            ClearSelection();
            Render();
        }

        void ClearSelection() { selHand = -1; selField = -1; }

        /// <summary>動作確認用：置ける手札を交互に置き、最後に自分の魔法を1枚選ぶ</summary>
        public void Demo(int moves)
        {
            for (int m = 0; m < moves; m++)
            {
                var p = m % 2 == 0;
                var s = state.Get(p);
                var placed = false;
                for (int h = 0; h < s.Hand.Count && !placed; h++)
                    for (int zi = 0; zi < game.Rules.Zones.Count && !placed; zi++)
                    {
                        var next = state.Step(game.Rules, Choice.Place(p, h, zi, true));
                        if (next == null) continue;
                        log.Add($"{Who(p)}：{s.Hand[h].Name} を{game.Rules.Zones[zi].Name}に表側で置く");
                        state = next;
                        placed = true;
                    }
                if (!placed)
                {
                    var next = state.Step(game.Rules, Choice.Draw(p));
                    if (next != null) { log.Add($"{Who(p)}：ドロー"); state = next; }
                }
            }
            var f = state.Get(true).Field;
            selPlayer = true;
            // 攻撃できるカードがあればそれを、なければ発動できるカードを選ぶ
            selField = f.FindIndex(sl => sl.FaceUp && MatchState.Fights(game.Rules, sl));
            if (selField < 0) selField = f.FindIndex(sl => sl.Card.Effects.Any(e => e is Activated));
            Render();
        }

        static string Who(bool p) => p ? "自分" : "相手";

        void Do(Choice ch, string message)
        {
            var next = state.Step(game.Rules, ch);
            if (next == null) { log.Add($"（できません）{message}"); Render(); return; }
            state = next;
            log.Add(message);
            ClearSelection();
            Render();
        }

        // ---- 無効の状態 ----

        /// <summary>フィールドのカードごとの状態（有効・無効・順番次第）</summary>
        Dictionary<(bool, int), string> NegationStatus(out string summary)
        {
            var insts = state.FieldInsts(game.Rules);
            var stables = Negation.StableStates(insts.Select(x => x.inst).ToList());
            var result = new Dictionary<(bool, int), string>();
            if (stables == null) { summary = "フィールドのカードが多すぎるため、無効の状態は計算していません"; return result; }
            if (stables.Count == 0)
            {
                summary = "どの状態も安定しません（判定が止まらない盤面です）";
                foreach (var x in insts) result[(x.player, x.index)] = "？";
                return result;
            }
            for (int i = 0; i < insts.Count; i++)
            {
                var on = stables.Select(s => s[i]).Distinct().ToList();
                result[(insts[i].player, insts[i].index)] = on.Count > 1 ? "順番次第" : on[0] ? "有効" : "無効";
            }
            summary = stables.Count == 1 ? "無効の状態は1通りに決まります" : $"安定な状態が {stables.Count} 通りあり、適用の順番で変わります";
            return result;
        }

        /// <summary>効果が無効になっているカードの位置（攻撃力の計算に使う）</summary>
        static List<(bool, int)> NegList(Dictionary<(bool, int), string> neg) =>
            neg.Where(kv => kv.Value == "無効").Select(kv => kv.Key).ToList();

        static string ActionText(Action a) => a switch
        {
            Destroy d => NodeView.SelectorSummary(d.Target).Replace("\n", "・") + "を破壊",
            Bounce b => NodeView.SelectorSummary(b.Target).Replace("\n", "・") + "を手札に戻す",
            DrawCards dc => $"{dc.Count}枚ドロー",
            Damage dm => $"相手に{dm.Amount}ダメージ",
            Heal h => $"ライフを{h.Amount}回復",
            _ => "",
        };

        /// <summary>勝敗（どちらかのライフが 0 なら）</summary>
        string Winner()
        {
            if (game.Rules.Life == 0) return null;
            var l1 = state.P1.Life == 0;
            var l2 = state.P2.Life == 0;
            if (l1 && l2) return "引き分け（お互いのライフが 0）";
            if (l2) return "自分の勝ち（相手のライフが 0）";
            if (l1) return "相手の勝ち（自分のライフが 0）";
            return null;
        }

        // ---- 表示 ----

        static Label Text(string s, int size = 12, Color? color = null, bool bold = false)
        {
            var l = new Label(s);
            l.style.whiteSpace = WhiteSpace.Normal;
            l.style.fontSize = size;
            if (color.HasValue) l.style.color = color.Value;
            if (bold) l.style.unityFontStyleAndWeight = FontStyle.Bold;
            return l;
        }

        static VisualElement Row()
        {
            var r = new VisualElement();
            r.style.flexDirection = FlexDirection.Row;
            r.style.flexWrap = Wrap.Wrap;
            r.style.alignItems = Align.FlexStart;
            return r;
        }

        VisualElement Chip(Card c, bool faceUp, string status, bool selected, System.Action onClick, string stats = null)
        {
            var b = new Button(onClick);
            b.style.width = 120;
            b.style.minHeight = 64;
            b.style.marginRight = 6;
            b.style.marginBottom = 6;
            b.style.flexDirection = FlexDirection.Column;
            b.style.alignItems = Align.FlexStart;
            b.style.paddingLeft = 6;
            b.style.paddingTop = 4;
            var color = NodeView.KindColor(NodeKind.Card);
            b.style.backgroundColor = faceUp ? new Color(0.24f, 0.22f, 0.2f) : new Color(0.2f, 0.2f, 0.26f);
            b.style.borderLeftWidth = b.style.borderRightWidth = b.style.borderTopWidth = b.style.borderBottomWidth = selected ? 2 : 1;
            var bc = selected ? new Color(1f, 0.85f, 0.3f) : color;
            b.style.borderLeftColor = b.style.borderRightColor = b.style.borderTopColor = b.style.borderBottomColor = bc;
            b.Add(Text(c.Name, 11, Color.white, true));
            b.Add(Text(c.Type + (faceUp ? "" : "・裏側"), 10, Quiet));
            if (stats != null) b.Add(Text(stats, 10, new Color(0.85f, 0.8f, 0.6f)));
            if (status != null)
                b.Add(Text(status, 10, status == "有効" ? Good : status == "無効" ? Bad : Warn, true));
            return b;
        }

        VisualElement PlayerBoard(bool p, Dictionary<(bool, int), string> neg)
        {
            var s = state.Get(p);
            var box = new VisualElement();
            box.style.marginBottom = 12;
            box.style.paddingLeft = 10;
            box.style.paddingRight = 10;
            box.style.paddingTop = 8;
            box.style.paddingBottom = 4;
            box.style.backgroundColor = new Color(0.15f, 0.15f, 0.17f);
            box.style.borderTopLeftRadius = box.style.borderTopRightRadius = box.style.borderBottomLeftRadius = box.style.borderBottomRightRadius = 6;

            var head = Row();
            head.style.alignItems = Align.Center;
            head.Add(Text(Who(p), 15, Color.white, true));
            if (game.Rules.Life > 0)
                head.Add(Text($"　ライフ {s.Life}", 15, s.Life == 0 ? Bad : Good, true));
            head.Add(Text($"　デッキ {s.Deck.Count} 枚・墓地 {s.Grave.Count} 枚", 12, Quiet));
            var draw = new Button(() => Do(Choice.Draw(p), $"{Who(p)}：ドロー")) { text = "ドロー" };
            draw.style.marginLeft = 12;
            head.Add(draw);
            box.Add(head);

            var zones = new VisualElement();
            // 相手のフィールドは自分のフィールドを逆さまにした形（共通ルール②）なので、ゾーンの並びも逆にする
            var order = Enumerable.Range(0, game.Rules.Zones.Count).ToList();
            if (!p) order.Reverse();
            foreach (var zi in order)
            {
                var z = game.Rules.Zones[zi];
                if (z.Role != ZoneRole.Plain) continue;
                var zr = Row();
                zr.style.alignItems = Align.Center;
                zr.style.marginTop = 6;
                var title = Text($"{z.Name}（{z.Count}マス）", 11, NodeView.KindColor(NodeKind.Zone), true);
                title.style.width = 170;
                zr.Add(title);
                var cards = s.Field.Select((sl, i) => (sl, i)).Where(x => x.sl.Zone == zi).ToList();
                foreach (var (sl, i) in cards)
                {
                    neg.TryGetValue((p, i), out var st);
                    int idx = i;
                    string stats = null;
                    if (MatchState.Fights(game.Rules, sl))
                    {
                        var atk = state.AtkOf(game.Rules, NegList(neg), (p, i), sl);
                        stats = $"攻 {atk}" + (atk != sl.Card.Attack ? $"（元 {sl.Card.Attack}）" : "") + $"・守 {sl.Card.Defense}";
                    }
                    zr.Add(Chip(sl.Card, sl.FaceUp, st, selPlayer == p && selField == idx, () => { selPlayer = p; selField = idx; selHand = -1; Render(); }, stats));
                }
                if (z.Capacity == Capacity.One)
                    for (int k = cards.Count; k < z.Count; k++)
                    {
                        var empty = new VisualElement();
                        empty.style.width = 120;
                        empty.style.height = 64;
                        empty.style.marginRight = 6;
                        empty.style.marginBottom = 6;
                        empty.style.borderLeftWidth = empty.style.borderRightWidth = empty.style.borderTopWidth = empty.style.borderBottomWidth = 1;
                        empty.style.borderLeftColor = empty.style.borderRightColor = empty.style.borderTopColor = empty.style.borderBottomColor = Line;
                        zr.Add(empty);
                    }
                zones.Add(zr);
            }

            var hand = Row();
            hand.style.marginTop = 8;
            var ht = Text("手札", 11, Quiet, true);
            ht.style.width = 170;
            hand.Add(ht);
            for (int i = 0; i < s.Hand.Count; i++)
            {
                int idx = i;
                hand.Add(Chip(s.Hand[i], true, null, selPlayer == p && selHand == idx, () => { selPlayer = p; selHand = idx; selField = -1; Render(); }));
            }

            // 相手のフィールドは自分のフィールドを逆さまにした形（共通ルール②）
            if (p) { box.Add(zones); box.Add(hand); }
            else { box.Add(hand); box.Add(zones); }
            return box;
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
            var b = new Button(a) { text = text };
            b.style.marginTop = 4;
            side.Add(b);
        }

        void Render()
        {
            if (game == null) return;
            var neg = NegationStatus(out var negSummary);
            boards.Clear();
            boards.Add(PlayerBoard(false, neg));
            boards.Add(PlayerBoard(true, neg));

            side.Clear();
            var top = Row();
            top.style.alignItems = Align.Center;
            top.Add(Text("テストプレイ", 16, Color.white, true));
            var restart = new Button(() => { seed++; Start(game); }) { text = "最初から（混ぜ直す）" };
            restart.style.marginLeft = 12;
            top.Add(restart);
            side.Add(top);
            side.Add(Text("両方のプレイヤーを動かせます。カードを選ぶと、できる動きが出ます。", 11, Quiet));

            Section("選んでいるカード");
            var s = state.Get(selPlayer);
            if (selHand >= 0 && selHand < s.Hand.Count)
            {
                var c = s.Hand[selHand];
                side.Add(Text($"{Who(selPlayer)}の手札：{c.Name}（{c.Type}）", 12, Color.white));
                bool any = false;
                for (int zi = 0; zi < game.Rules.Zones.Count; zi++)
                    foreach (var up in new[] { true, false })
                    {
                        var ch = Choice.Place(selPlayer, selHand, zi, up);
                        if (state.Step(game.Rules, ch) == null) continue;
                        any = true;
                        var zname = game.Rules.Zones[zi].Name;
                        var msg = $"{Who(selPlayer)}：{c.Name} を{zname}に{(up ? "表側" : "裏側")}で置く";
                        ActionButton($"{zname}に{(up ? "表側" : "裏側")}で置く", () => Do(ch, msg));
                    }
                if (!any) side.Add(Text("置けるゾーンがありません", 12, Warn));
            }
            else if (selField >= 0 && selField < s.Field.Count)
            {
                var sl = s.Field[selField];
                side.Add(Text($"{Who(selPlayer)}のフィールド：{sl.Card.Name}（{sl.Card.Type}・{(sl.FaceUp ? "表側" : "裏側")}）", 12, Color.white));
                neg.TryGetValue((selPlayer, selField), out var st);
                if (st != null) side.Add(Text($"効果の状態：{st}", 12, st == "有効" ? Good : st == "無効" ? Bad : Warn));
                for (int e = 0; e < sl.Card.Effects.Count; e++)
                {
                    if (!(sl.Card.Effects[e] is Activated act)) continue;
                    var what = string.Join("、", act.Actions.Select(ActionText));
                    int ei = e;
                    if (st != "無効")
                        ActionButton($"発動する（{what}）", () => Do(Choice.Resolve(selPlayer, selField, ei, true), $"{Who(selPlayer)}：{sl.Card.Name} を発動（{what}）"));
                    if (st != "有効")
                        ActionButton("無効にされた状態で解決する（何も起きない）", () => Do(Choice.Resolve(selPlayer, selField, ei, false), $"{Who(selPlayer)}：{sl.Card.Name} を発動したが無効"));
                }
                foreach (var n in sl.Card.Effects.OfType<Negate>())
                    side.Add(Text($"永続効果：{NodeView.SelectorSummary(n.Target).Replace("\n", "・")}の効果を無効にする", 11, Quiet));
                foreach (var bo in sl.Card.Effects.OfType<Boost>())
                    side.Add(Text($"永続効果：{NodeView.SelectorSummary(bo.Target).Replace("\n", "・")}の攻撃力を{(bo.Amount >= 0 ? "+" : "")}{bo.Amount}", 11, Quiet));
                if (sl.FaceUp && MatchState.Fights(game.Rules, sl))
                {
                    var negs = NegList(neg);
                    var a = state.AtkOf(game.Rules, negs, (selPlayer, selField), sl);
                    var o = !selPlayer;
                    var of = state.Get(o).Field;
                    int pk = selField;
                    bool pp = selPlayer;
                    for (int j = 0; j < of.Count; j++)
                    {
                        if (!state.TargetOK(game.Rules, pp, j)) continue;
                        var tl = of[j];
                        var vs = tl.FaceUp ? $"攻撃力 {state.AtkOf(game.Rules, negs, (o, j), tl)}" : $"裏側・守備力 {tl.Card.Defense}";
                        var name = tl.FaceUp ? tl.Card.Name : "裏側のカード";
                        int tj = j;
                        ActionButton($"{name}を攻撃する（{a} 対 {vs}）",
                            () => Do(Choice.Attack(pp, pk, tj, negs), $"{Who(pp)}：{sl.Card.Name}（{a}）で{name}（{vs}）を攻撃"));
                    }
                    if (state.TargetOK(game.Rules, pp, null))
                        ActionButton($"直接攻撃する（{a} ダメージ）", () => Do(Choice.Attack(pp, pk, null, negs), $"{Who(pp)}：{sl.Card.Name}で直接攻撃（{a}）"));
                }
            }
            else side.Add(Text("（なし）", 12, Quiet));

            var winner = Winner();
            if (winner != null)
            {
                Section("勝敗");
                side.Add(Text(winner, 14, Warn, true));
            }

            Section("無効の状態");
            side.Add(Text(negSummary, 12, negSummary.Contains("1通り") ? Good : Warn));

            Section("盤面の制約");
            var v = state.Violations(game.Rules);
            if (v.Count == 0) side.Add(Text("すべて成り立っています（枚数・置けるゾーン・マスの数。Lean で証明済み）", 12, Good));
            foreach (var m in v) side.Add(Text("・" + m, 12, Bad));

            Section("記録");
            foreach (var m in Enumerable.Reverse(log).Take(20)) side.Add(Text(m, 11, Quiet));
        }
    }
}
