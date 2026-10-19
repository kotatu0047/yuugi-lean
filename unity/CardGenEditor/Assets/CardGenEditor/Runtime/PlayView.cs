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
    /// 無効の状態は、カードが適用された順番を覚えておき、動きのたびに OCG の手順（Lean の Timed.lean の
    /// TSys.succ。C# 版は差分テスト済み）で判定を進めて決める。先に適用された効果が勝つので、
    /// 例えば相手の Bloo－D がいるところに自分の Bloo－D を出すと、自分の Bloo－D が無効になる。
    /// 手順の途中でプレイヤーが選ぶ場面（同じプレイヤーのカードを複数、有効に戻せるときなど）だけ選択肢を出す。
    /// ターンは C# の Match（Lean の Turn.lean の Match.step? と差分テスト済み）で進める。カードを置く・攻撃するのは
    /// ターンプレイヤーだけ（場のカードの発動はどちらのターンでもできる）、召喚は1ターンにルールの回数まで、攻撃は1ターンに
    /// 1枚1回まで。「ターン終了」で相手のターンになり、新しいターンプレイヤーがルールの枚数を引く。
    /// マスの位置があるゾーンは、盤面のマス目の並び（相手が上、自分が下）で表示し、空いているマスをクリックして置ける。
    /// マナを使うルールでは、ターンプレイヤーがマナを出すカードをタップしてマナを得て、コストを払ってカードを置く。
    /// </summary>
    public sealed class PlayView : VisualElement
    {
        Game game;
        Match match;
        MatchState state => match.G;
        int seed = 1;
        // ターン：先攻のプレイヤー、今のターンプレイヤー、何ターン目か
        bool firstPlayer = true;
        bool turn => match.Turn.Tp;
        int turnCount => match.Turn.Count;
        readonly List<string> log = new List<string>();

        // 無効の判定（適用された順番を覚えておく。C# のコアの Judge）
        Judge judge = new Judge();

        // 選んでいるカード
        bool selPlayer;
        int selHand = -1;
        int selField = -1;
        // 手札を置くときに表側で置くか
        bool placeUp = true;

        readonly VisualElement boards;
        readonly VisualElement side;

        static readonly Color Panel = new Color(0.16f, 0.16f, 0.18f);
        static readonly Color Line = new Color(0.3f, 0.3f, 0.33f);
        static readonly Color Good = new Color(0.45f, 0.8f, 0.5f);
        static readonly Color Bad = new Color(0.95f, 0.45f, 0.4f);
        static readonly Color Warn = new Color(0.95f, 0.75f, 0.35f);
        static readonly Color Quiet = new Color(0.7f, 0.7f, 0.75f);
        // フィールドのマス1つの高さ（カードの表示と空きのマスで揃える）
        const float CellHeight = 100;

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
            // マナを出すカード（土地）があれば、デッキの 4 割ほどをそれにする（マナが足りずに動けなくならないように）
            var lands = game.Cards.Where(c => c.Mana > 0).ToList();
            var others = game.Cards.Where(c => c.Mana == 0).ToList();
            var n = game.Rules.DeckSize;
            var nl = lands.Count == 0 || others.Count == 0 ? 0 : n * 2 / 5;
            var d = lands.Count == 0 || others.Count == 0
                ? Enumerable.Range(0, n).Select(i => game.Cards[i % game.Cards.Count]).ToList()
                : Enumerable.Range(0, nl).Select(i => lands[i % lands.Count])
                    .Concat(Enumerable.Range(0, n - nl).Select(i => others[i % others.Count])).ToList();
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
            match = Match.Start(g.Rules, MakeDeck(rng), MakeDeck(rng), firstPlayer);
            log.Clear();
            judge = new Judge();
            judge.Sync(state, g.Rules, turn);
            log.Add($"開始（混ぜ方 {seed}）：お互いに {g.Rules.HandSize} 枚引きました。先攻は{Who(firstPlayer)}" +
                    (g.Rules.FirstTurnDraw ? $"（先攻も {g.Rules.DrawPerTurn} 枚引きました）" : ""));
            log.Add($"── 第1ターン：{Who(turn)}のターン ──");
            ClearSelection();
            Render();
        }

        void ClearSelection() { selHand = -1; selField = -1; }

        /// <summary>ターンを終えて、相手のターンにする。新しいターンプレイヤーはルールの枚数を引く</summary>
        void EndTurn()
        {
            var q = !turn;
            var before = state.Get(q).Hand.Count;
            match = match.Step(game.Rules, TChoice.EndTurn());
            log.Add($"── 第{turnCount}ターン：{Who(turn)}のターン ──");
            var drawn = state.Get(q).Hand.Count - before;
            if (game.Rules.DrawPerTurn > 0)
                log.Add(drawn == game.Rules.DrawPerTurn ? $"{Who(q)}：{drawn} 枚ドロー" : $"{Who(q)}：デッキが足りず {drawn} 枚だけ引きました");
            judge.Sync(state, game.Rules, turn);
            ClearSelection();
        }

        /// <summary>動作確認用：ターンごとに置ける手札を1枚置いてターンを終え、最後に自分のカードを1枚選ぶ</summary>
        public void Demo(int moves)
        {
            for (int m = 0; m < moves; m++)
            {
                if (m > 0) EndTurn();
                var p = turn;
                for (int k = 0; k < state.Get(p).Field.Count; k++)
                {
                    var tapped = match.Step(game.Rules, TChoice.Tap(k));
                    if (tapped == null) continue;
                    log.Add($"{Who(p)}：{state.Get(p).Field[k].Card.Name} をタップ（マナ +{state.Get(p).Field[k].Card.Mana}）");
                    match = tapped;
                }
                var s = state.Get(p);
                var placed = false;
                for (int h = 0; h < s.Hand.Count && !placed; h++)
                    for (int zi = 0; zi < game.Rules.Zones.Count && !placed; zi++)
                    {
                        var cell = state.FreeCell(game.Rules, p, zi);
                        var next = match.Step(game.Rules, TChoice.Place(h, zi, cell, true));
                        if (next == null) continue;
                        log.Add($"{Who(p)}：{s.Hand[h].Name} を{CellName(zi, cell)}に表側で置く");
                        match = next;
                        judge.Sync(state, game.Rules, turn);
                        placed = true;
                    }
            }
            // MTG 式の戦闘なら、攻撃を宣言してブロックの場面を見せる
            if (game.Rules.Blocking)
                for (int k = 0; k < state.Get(turn).Field.Count; k++)
                {
                    var next = match.Step(game.Rules, TChoice.Attack(k, null, new List<(bool, int)>()));
                    if (next == null) continue;
                    log.Add($"{Who(turn)}：{state.Get(turn).Field[k].Card.Name} で攻撃");
                    match = next;
                    Render();
                    return;
                }
            var f = state.Get(true).Field;
            selPlayer = true;
            // 攻撃できるカードがあればそれを、なければ発動できるカードを選ぶ
            selField = f.FindIndex(sl => sl.FaceUp && MatchState.Fights(game.Rules, sl));
            if (selField < 0) selField = f.FindIndex(sl => sl.Card.Effects.Any(e => e is Activated));
            Render();
        }

        static string Who(bool p) => p ? "自分" : "相手";

        /// <summary>ゾーンの何番目のマスか（表示用。1 から数える）</summary>
        string CellName(int zi, int cell)
        {
            var z = game.Rules.Zones[zi];
            return z.Capacity == Capacity.One && z.Count > 1 ? $"{z.Name}の{cell + 1}番目のマス" : z.Name;
        }

        /// <summary>手札のカードを、ゾーン zi の cell 番目のマスに置く動き（選んでいる手札と表裏で）</summary>
        void PlaceSelected(int zi, int cell)
        {
            var c = state.Get(selPlayer).Hand[selHand];
            Do(TChoice.Place(selHand, zi, cell, placeUp), $"{Who(selPlayer)}：{c.Name} を{CellName(zi, cell)}に{(placeUp ? "表側" : "裏側")}で置く");
        }

        /// <summary>選んでいる手札を、ゾーン zi の cell 番目のマスに置けるか</summary>
        bool CanPlaceSelected(bool p, int zi, int cell) =>
            selHand >= 0 && selPlayer == p && p == turn && selHand < state.Get(p).Hand.Count &&
            match.Step(game.Rules, TChoice.Place(selHand, zi, cell, placeUp)) != null;

        void Do(TChoice ch, string message)
        {
            var next = match.Step(game.Rules, ch);
            if (next == null) { log.Add($"（できません）{message}"); Render(); return; }
            match = next;
            log.Add(message);
            judge.Sync(state, game.Rules, turn);
            ClearSelection();
            Render();
        }

        /// <summary>マナやタップを使うルールか（カードにコストかマナがあるか、攻撃でタップするか）</summary>
        bool UsesMana => game.Rules.AttackTaps || game.Cards.Any(c => c.Cost > 0 || c.Mana > 0);

        /// <summary>置く場所はあるのに置けない理由（召喚の上限・種類ごとの上限・マナ）。置けるなら null</summary>
        string PlaceBlocked(Slot sl)
        {
            var r = game.Rules;
            var t = match.Turn;
            if (MatchState.Fights(r, sl) && r.SummonsPerTurn != 0 && t.Summons >= r.SummonsPerTurn)
                return $"このターンはもう召喚できません（1ターンに {r.SummonsPerTurn} 回まで）";
            foreach (var l in r.PlaceLimits)
                if (l.Types.Contains(sl.Card.Type) && t.Placed.Count(l.Types.Contains) >= l.Count)
                    return $"このターンはもう「{string.Join("・", l.Types)}」を置けません（1ターンに {l.Count} 枚まで）";
            if (sl.Card.Cost > t.Pool)
                return $"マナが足りません（コスト {sl.Card.Cost}・今のマナ {t.Pool}）。マナを出すカードを選んでタップしてください";
            return null;
        }

        // ---- 無効の状態 ----

        /// <summary>判定の途中の選択肢を選ぶ</summary>
        void Choose(int k, string text)
        {
            log.Add($"無効の判定：{text}");
            judge.Choose(k);
            Render();
        }

        string ChoiceText((bool player, int index, Slot slot) c) =>
            $"{Who(c.player)}の{c.slot.Card.Name}を{(judge.ChoosingKill ? "無効にする" : "有効に戻す（効果の適用を始める）")}";

        string JudgeNote() => judge.Result switch
        {
            Judge.Outcome.Unique => "無効の状態は、カードが適用された順番から1通りに決まります（先に適用された効果が勝つ）",
            Judge.Outcome.Done => "判定が終わりました",
            Judge.Outcome.Loop => "判定が止まりません（同じ状態に戻りました）。この盤面では無効の状態が決まりません",
            _ => judge.Outlook.MayLoop ? "判定の途中です。選び方によっては判定が止まりません" :
                 judge.Outlook.TooMany ? "判定の途中です" : $"判定の途中です。選び方によって結果が {judge.Outlook.Ends.Count} 通りに分かれます",
        };

        string ChooserText()
        {
            if (judge.ChoosingKill) return "無効にするカードが複数あり、どれからにするかで結果が変わります。順番を選んでください";
            var who = Who(judge.Choices[0].card.player);
            return $"有効に戻せる{who}のカードが複数あります。{who}が、どれから適用するかを選びます（OCG の手順）";
        }

        /// <summary>フィールドのカードごとの状態（有効・無効）</summary>
        Dictionary<(bool, int), string> NegationStatus(out string summary)
        {
            var result = new Dictionary<(bool, int), string>();
            foreach (var (p, i, _) in state.FieldInsts(game.Rules))
                result[(p, i)] = judge.IsOn(state.Get(p).Field[i]) ? "有効" : "無効";
            summary = JudgeNote();
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
            b.style.minHeight = CellHeight;
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
            if (p == turn) head.Add(Text("　ターン中", 12, Warn, true));
            if (game.Rules.Life > 0)
                head.Add(Text($"　ライフ {s.Life}", 15, s.Life == 0 ? Bad : Good, true));
            head.Add(Text($"　デッキ {s.Deck.Count} 枚・墓地 {s.Grave.Count} 枚", 12, Quiet));
            if (p == turn)
            {
                var end = new Button(() => { EndTurn(); Render(); }) { text = "ターン終了" };
                end.style.marginLeft = 12;
                head.Add(end);
            }
            box.Add(head);

            var zones = new VisualElement();
            // 相手のフィールドは自分のフィールドを逆さまにした形（共通ルール②）なので、ゾーンの並びも逆にする。
            // マスの位置があるゾーンは、真ん中のマス目の表示（GridBoard）に出す
            var order = Enumerable.Range(0, game.Rules.Zones.Count).ToList();
            if (!p) order.Reverse();
            foreach (var zi in order)
            {
                var z = game.Rules.Zones[zi];
                if (z.Role != ZoneRole.Plain || z.Cells.Count > 0) continue;
                var zr = Row();
                zr.style.alignItems = Align.Center;
                zr.style.marginTop = 6;
                var title = Text($"{z.Name}（{z.Count}マス）", 11, NodeView.KindColor(NodeKind.Zone), true);
                title.style.width = 170;
                zr.Add(title);
                if (z.Capacity == Capacity.One)
                {
                    var cells = Enumerable.Range(0, z.Count).ToList();
                    if (!p) cells.Reverse();
                    foreach (var k in cells) zr.Add(CellView(p, zi, k, neg));
                }
                else
                {
                    foreach (var (sl, i) in s.Field.Select((sl, i) => (sl, i)).Where(x => x.sl.Zone == zi))
                        zr.Add(SlotChip(p, i, sl, neg));
                    if (CanPlaceSelected(p, zi, 0)) zr.Add(PlaceButton(zi, 0));
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
                var hc = s.Hand[i];
                hand.Add(Chip(hc, true, null, selPlayer == p && selHand == idx, () => { selPlayer = p; selHand = idx; selField = -1; Render(); },
                    UsesMana && (hc.Cost > 0 || hc.Mana > 0) ? $"コスト {hc.Cost}" + (hc.Mana > 0 ? $"・{hc.Mana}マナ" : "") : null));
            }

            // 相手のフィールドは自分のフィールドを逆さまにした形（共通ルール②）
            if (p) { box.Add(zones); box.Add(hand); }
            else { box.Add(hand); box.Add(zones); }
            return box;
        }

        /// <summary>フィールドのカード1枚の表示（クリックで選ぶ）</summary>
        VisualElement SlotChip(bool p, int i, Slot sl, Dictionary<(bool, int), string> neg)
        {
            neg.TryGetValue((p, i), out var st);
            string stats = null;
            if (MatchState.Fights(game.Rules, sl))
            {
                var atk = state.AtkOf(game.Rules, NegList(neg), (p, i), sl);
                stats = $"攻 {atk}" + (atk != sl.Card.Attack ? $"（元 {sl.Card.Attack}）" : "") + $"・守 {sl.Card.Defense}";
            }
            var f = state.Get(p).Field;
            var tapped = UsesMana && TappedAt(p, i);
            if (UsesMana)
            {
                var notes = new List<string>();
                if (tapped) notes.Add("タップ中");
                if (sl.Card.Mana > 0) notes.Add($"{sl.Card.Mana}マナ");
                if (p == turn && match.Turn.Sick(game.Rules, f, sl)) notes.Add("召喚酔い");
                if (notes.Count > 0) stats = (stats == null ? "" : stats + "\n") + string.Join("・", notes);
            }
            var chip = Chip(sl.Card, sl.FaceUp, st, selPlayer == p && selField == i,
                () => { selPlayer = p; selField = i; selHand = -1; Render(); }, stats);
            if (tapped) chip.style.opacity = 0.6f;
            return chip;
        }

        /// <summary>
        /// p のフィールドの i 番目のカードをタップしている状態で表示するか。記録は「同じカードのうち何枚がタップしているか」
        /// だけなので（Lean のモデルと同じ）、同じカードが複数あれば前から順にその枚数をタップしている状態で表示する
        /// </summary>
        bool TappedAt(bool p, int i)
        {
            var f = state.Get(p).Field;
            var sl = f[i];
            var rec = p == turn ? match.Turn.Tapped : match.Turn.OppTapped;
            var before = f.Take(i + 1).Count(x => TurnInfo.SameSlot(x, sl));
            return before <= rec.Count(x => TurnInfo.SameSlot(x, sl));
        }

        /// <summary>空いているマスに置くボタン</summary>
        VisualElement PlaceButton(int zi, int cell)
        {
            var b = new Button(() => PlaceSelected(zi, cell)) { text = $"ここに{(placeUp ? "表側" : "裏側")}で置く" };
            b.style.width = 120;
            b.style.height = CellHeight;
            b.style.marginLeft = 0;
            b.style.marginRight = 6;
            b.style.marginBottom = 6;
            b.style.fontSize = 11;
            b.style.backgroundColor = new Color(0.22f, 0.3f, 0.22f);
            b.style.borderLeftColor = b.style.borderRightColor = b.style.borderTopColor = b.style.borderBottomColor = Good;
            return b;
        }

        /// <summary>空きのマス（置けない）</summary>
        VisualElement EmptyCell(string label)
        {
            var empty = new VisualElement();
            empty.style.width = 120;
            empty.style.height = CellHeight;
            empty.style.marginRight = 6;
            empty.style.marginBottom = 6;
            empty.style.borderLeftWidth = empty.style.borderRightWidth = empty.style.borderTopWidth = empty.style.borderBottomWidth = 1;
            empty.style.borderLeftColor = empty.style.borderRightColor = empty.style.borderTopColor = empty.style.borderBottomColor = Line;
            if (label != null)
            {
                var l = Text(label, 9, new Color(0.45f, 0.45f, 0.5f));
                l.style.paddingLeft = 4;
                l.style.paddingTop = 2;
                empty.Add(l);
            }
            return empty;
        }

        /// <summary>p のゾーン zi の k 番目のマス：カードがあれば表示、空いていれば（置けるなら）置くボタン</summary>
        VisualElement CellView(bool p, int zi, int k, Dictionary<(bool, int), string> neg, string emptyLabel = null)
        {
            var f = state.Get(p).Field;
            var i = f.FindIndex(sl => sl.Zone == zi && sl.Cell == k);
            if (i >= 0) return SlotChip(p, i, f[i], neg);
            if (CanPlaceSelected(p, zi, k)) return PlaceButton(zi, k);
            return EmptyCell(emptyLabel);
        }

        /// <summary>マスの位置があるゾーンを、盤面のマス目の並びで表示する（行の小さい方が上。見本では相手が上）</summary>
        VisualElement GridBoard(Dictionary<(bool, int), string> neg)
        {
            var at = new Dictionary<Cell, (bool p, int zi, int k)>();
            foreach (var p in new[] { false, true })
                for (int zi = 0; zi < game.Rules.Zones.Count; zi++)
                {
                    var z = game.Rules.Zones[zi];
                    if (z.Role != ZoneRole.Plain) continue;
                    for (int k = 0; k < z.Cells.Count; k++)
                    {
                        var c = game.Rules.CellOf(p, zi, k);
                        if (c.HasValue && !at.ContainsKey(c.Value)) at[c.Value] = (p, zi, k);
                    }
                }
            var box = new VisualElement();
            if (at.Count == 0) return box;
            box.style.marginBottom = 12;
            box.style.paddingLeft = 10;
            box.style.paddingTop = 8;
            box.style.paddingBottom = 4;
            box.style.backgroundColor = new Color(0.13f, 0.14f, 0.16f);
            box.style.borderTopLeftRadius = box.style.borderTopRightRadius = box.style.borderBottomLeftRadius = box.style.borderBottomRightRadius = 6;
            int c0 = at.Keys.Min(c => c.Col), c1 = at.Keys.Max(c => c.Col);
            int r0 = at.Keys.Min(c => c.Row), r1 = at.Keys.Max(c => c.Row);
            var head = Row();
            head.Add(Text($"フィールド（盤面のマス目の列 {c0}〜{c1}・行 {r0}〜{r1}。上が相手、下が自分）", 11, Quiet));
            box.Add(head);
            for (int r = r0; r <= r1; r++)
            {
                if (!at.Keys.Any(c => c.Row == r))
                {
                    // マスのない行（見本では盤面の中心の行）は細い区切りにする
                    var sep = Text($"行 {r}（マスなし）", 9, new Color(0.45f, 0.45f, 0.5f));
                    sep.style.marginTop = 2;
                    sep.style.marginBottom = 8;
                    sep.style.borderBottomWidth = 1;
                    sep.style.borderBottomColor = Line;
                    box.Add(sep);
                    continue;
                }
                var line = Row();
                line.style.flexWrap = Wrap.NoWrap;
                line.style.alignItems = Align.Center;
                var rowLabel = Text($"行 {r}", 10, Quiet);
                rowLabel.style.width = 40;
                line.Add(rowLabel);
                for (int c = c0; c <= c1; c++)
                {
                    if (!at.TryGetValue(new Cell(c, r), out var x))
                    {
                        var gap = new VisualElement();
                        gap.style.width = 126;
                        gap.style.height = CellHeight;
                        line.Add(gap);
                        continue;
                    }
                    line.Add(CellView(x.p, x.zi, x.k, neg, $"{Who(x.p)}の{game.Rules.Zones[x.zi].Name} {x.k + 1}"));
                }
                box.Add(line);
            }
            return box;
        }

        /// <summary>MTG 式の戦闘：攻撃されたプレイヤーが、ブロックするカードを選ぶ</summary>
        void BlockPanel(int k, Dictionary<(bool, int), string> neg)
        {
            var p = turn;
            var o = !p;
            var sl = state.Get(p).Field[k];
            var negs = NegList(neg);
            var a = state.AtkOf(game.Rules, negs, (p, k), sl);
            Section($"ブロック（{Who(o)}が選ぶ）");
            side.Add(Text($"{Who(p)}の{sl.Card.Name}（攻撃力 {a}・守備力 {sl.Card.Defense}）が攻撃しています", 12, Warn, true));
            var of = state.Get(o).Field;
            for (int j = 0; j < of.Count; j++)
            {
                var tl = of[j];
                if (!MatchState.Fights(game.Rules, tl)) continue;
                var b = state.AtkOf(game.Rules, negs, (o, j), tl);
                var dies = new List<string>();
                if (0 < a && tl.Card.Defense <= a) dies.Add(tl.Card.Name);
                if (0 < b && sl.Card.Defense <= b) dies.Add(sl.Card.Name);
                var result = dies.Count == 0 ? "どちらも残る" : string.Join("と", dies) + "を破壊";
                int jj = j;
                if (match.Step(game.Rules, TChoice.Block(jj, negs)) == null)
                {
                    var why = match.Turn.IsTapped(o, of, tl) ? "タップしている" : "このターンにもうブロックした";
                    side.Add(Text($"{tl.Card.Name}：{why}のでブロックできません", 11, Quiet));
                    continue;
                }
                ActionButton($"{tl.Card.Name}（{b}/{tl.Card.Defense}）でブロックする（{result}）",
                    () => Do(TChoice.Block(jj, negs), $"{Who(o)}：{tl.Card.Name}でブロック（{result}）"));
            }
            ActionButton($"ブロックしない（{Who(o)}に {a} ダメージ）",
                () => Do(TChoice.Block(null, negs), $"{Who(o)}：ブロックしない（{a} ダメージ）"));
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
            var restart = new Button(() => { seed++; Start(game); }) { text = "最初から（混ぜ直す）" };
            restart.style.marginLeft = 12;
            top.Add(restart);
            side.Add(top);
            var turnRow = Row();
            turnRow.style.alignItems = Align.Center;
            turnRow.style.marginTop = 6;
            turnRow.Add(Text($"第{turnCount}ターン：{Who(turn)}のターン", 14, Warn, true));
            var endTurn = new Button(() => { EndTurn(); Render(); }) { text = "ターン終了" };
            endTurn.style.marginLeft = 12;
            turnRow.Add(endTurn);
            var swap = new Button(() => { firstPlayer = !firstPlayer; Start(game); }) { text = $"{Who(!firstPlayer)}の先攻で最初から" };
            swap.style.marginLeft = 6;
            turnRow.Add(swap);
            side.Add(turnRow);
            var lim = game.Rules.SummonsPerTurn == 0 ? "制限なし" : $"{match.Turn.Summons}/{game.Rules.SummonsPerTurn}";
            side.Add(Text($"このターンの召喚：{lim}・攻撃したカード：{match.Turn.Attacked.Count} 枚", 11, Quiet));
            if (UsesMana)
                side.Add(Text($"{Who(turn)}のマナ：{match.Turn.Pool}（ターンの終わりに消えます）", 13, Good, true));
            if (game.Rules.PlaceLimits.Count > 0)
                side.Add(Text("このターンに置いた枚数：" + string.Join("・", game.Rules.PlaceLimits.Select(l =>
                    $"{string.Join("+", l.Types)} {match.Turn.Placed.Count(l.Types.Contains)}/{l.Count}")), 11, Quiet));
            side.Add(Text("両方のプレイヤーを動かせます。カードを置く・攻撃するのはターンプレイヤーだけで、場のカードの発動はどちらのターンでも" +
                          "できます。引くのはターンの最初だけです。カードを選ぶと、できる動きが出ます。", 11, Quiet));
            if (judge.Choices != null)
                side.Add(Text("無効の判定で、プレイヤーが選ぶ場面です（下の「無効の状態」から選んでください）", 12, Warn, true));
            if (match.Turn.Pending is int pend)
                BlockPanel(pend, neg);

            Section("選んでいるカード");
            var s = state.Get(selPlayer);
            if (selHand >= 0 && selHand < s.Hand.Count)
            {
                var c = s.Hand[selHand];
                side.Add(Text($"{Who(selPlayer)}の手札：{c.Name}（{c.Type}）", 12, Color.white));
                bool any = false;
                if (selPlayer != turn) { side.Add(Text($"{Who(turn)}のターンなので、{Who(selPlayer)}は手札を置けません", 12, Warn)); any = true; }
                else
                {
                    var upRow = Row();
                    upRow.style.alignItems = Align.Center;
                    upRow.Add(Text("置く向き：", 12, Quiet));
                    foreach (var up in new[] { true, false })
                    {
                        var u = up;
                        var b = new Button(() => { placeUp = u; Render(); }) { text = (up ? "表側" : "裏側") + (placeUp == up ? "（選択中）" : "") };
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
                            var why = PlaceBlocked(new Slot(zi, cell, c, placeUp));
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
                for (int e = 0; e < sl.Card.Effects.Count; e++)
                {
                    if (!(sl.Card.Effects[e] is Activated act)) continue;
                    var what = string.Join("、", act.Actions.Select(ActionText));
                    int ei = e;
                    if (st != "無効")
                        ActionButton($"発動する（{what}）", () => Do(TChoice.Resolve(selPlayer, selField, ei, true), $"{Who(selPlayer)}：{sl.Card.Name} を発動（{what}）"));
                    if (st != "有効")
                        ActionButton("無効にされた状態で解決する（何も起きない）", () => Do(TChoice.Resolve(selPlayer, selField, ei, false), $"{Who(selPlayer)}：{sl.Card.Name} を発動したが無効"));
                }
                if (sl.Card.Mana > 0)
                {
                    if (selPlayer != turn)
                        side.Add(Text($"{Who(turn)}のターンなので、タップしてマナを出せません", 12, Quiet));
                    else if (match.Turn.TapOK(game.Rules, s.Field, sl))
                    {
                        int tk = selField;
                        ActionButton($"タップしてマナを出す（+{sl.Card.Mana}）", () => Do(TChoice.Tap(tk), $"{Who(turn)}：{sl.Card.Name} をタップ（マナ +{sl.Card.Mana}）"));
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
                if (sl.FaceUp && MatchState.Fights(game.Rules, sl) && selPlayer != turn)
                    side.Add(Text($"{Who(turn)}のターンなので攻撃できません", 12, Quiet));
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
                        ActionButton($"攻撃する（攻撃力 {a}。{Who(o)}がブロックするかを選ぶ）",
                            () => Do(TChoice.Attack(pk, null, negs), $"{Who(pp)}：{sl.Card.Name}（{a}）で攻撃"));
                        of = new List<Slot>();
                    }
                    for (int j = 0; j < of.Count; j++)
                    {
                        if (!state.TargetOK(game.Rules, pp, j)) continue;
                        var tl = of[j];
                        var vs = tl.FaceUp ? $"攻撃力 {state.AtkOf(game.Rules, negs, (o, j), tl)}" : $"裏側・守備力 {tl.Card.Defense}";
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

            var winner = Winner();
            if (winner != null)
            {
                Section("勝敗");
                side.Add(Text(winner, 14, Warn, true));
            }

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
