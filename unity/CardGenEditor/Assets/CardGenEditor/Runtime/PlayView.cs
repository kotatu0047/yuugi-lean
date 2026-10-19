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
    /// インスタントは、ターンプレイヤーでない方も、自分のカードをタップして出したマナで置ける。スタックのルールでは、
    /// 呪文は後に置いたものから解決する。MTG 式の戦闘では、攻撃するカードを何枚でも宣言し、守る側がブロックを割り当てる。
    /// </summary>
    public sealed partial class PlayView : VisualElement
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
        // 手札を置くときに払うマナ（null なら自動の払い方）
        List<string> customPay;
        // MTG 式の戦闘で、守る側が割り当てたブロック（ブロックするカードの位置 → 何番目の攻撃か）
        readonly Dictionary<int, int> blockPlan = new Dictionary<int, int>();
        // 対象を選んでいる発動（プレイヤー・フィールドの位置・効果の番号・説明）
        (bool p, int k, int e, string what)? targeting;

        readonly ScrollView boardScroll;
        readonly VisualElement boards;
        readonly VisualElement side;
        // 右の欄の動きのボタン（右クリックのメニューにも出す）：選んでいるカードの動きと、それ以外（対象・スタック・ブロックなど）
        readonly List<MenuEntry> selectionActions = new List<MenuEntry>();
        readonly List<MenuEntry> panelActions = new List<MenuEntry>();
        bool inSelection;

        /// <summary>「エディタに戻る」（アプリが設定する）</summary>
        public System.Action Exit;

        static readonly Color Panel = Theme.Panel;
        static readonly Color Line = Theme.Line;
        static readonly Color Good = Theme.Green;
        static readonly Color Bad = Theme.Red;
        static readonly Color Warn = Theme.Amber;
        static readonly Color Quiet = Theme.Muted;
        // フィールドのマス1つの高さ（カードの表示と空きのマスで揃える）
        const float CellHeight = 100;

        public PlayView()
        {
            style.flexGrow = 1;
            style.flexDirection = FlexDirection.Row;
            boardScroll = new ScrollView(ScrollViewMode.VerticalAndHorizontal);
            boardScroll.style.flexGrow = 1;
            boardScroll.style.backgroundColor = Theme.Deep;
            boards = new VisualElement();
            boards.style.paddingLeft = 16;
            boards.style.paddingRight = 16;
            boards.style.paddingTop = 8;
            boardScroll.Add(boards);
            Add(boardScroll);
            PopupMenu.Attach(boardScroll, _ => GeneralMenu());
            var sideScroll = new ScrollView();
            sideScroll.style.width = 420;
            sideScroll.style.backgroundColor = Panel;
            sideScroll.style.borderLeftWidth = 1;
            sideScroll.style.borderLeftColor = Theme.LineHi;
            side = new VisualElement();
            side.style.paddingLeft = 12;
            side.style.paddingRight = 12;
            side.style.paddingTop = 10;
            sideScroll.Add(side);
            Add(sideScroll);
            PopupMenu.Attach(sideScroll, _ => GeneralMenu());
            RegisterDragEvents();
        }

        /// <summary>カードの一覧から山札を作る（土地は色のコストに合わせて選び、山札全体にむらなく散らす。C# の中核の DeckBuilder）</summary>
        List<Card> MakeDeck(System.Random rng) => DeckBuilder.Make(game, rng);

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

        void ClearSelection() { selHand = -1; selField = -1; customPay = null; }

        /// <summary>ターンプレイヤーの手札が上限を超えている枚数（上限がないか、超えていなければ 0）</summary>
        int OverHand => game.Rules.HandLimit == 0 ? 0 : Math.Max(0, state.Get(turn).Hand.Count - game.Rules.HandLimit);

        /// <summary>手札の上限まで、後ろのカードから捨てる（デモ用）</summary>
        void DiscardDown()
        {
            while (OverHand > 0)
            {
                var h = state.Get(turn).Hand.Count - 1;
                var name = state.Get(turn).Hand[h].Name;
                var next = match.Step(game.Rules, TChoice.Discard(h));
                if (next == null) break;
                log.Add($"{Who(turn)}：{name} を捨てる（手札の上限 {game.Rules.HandLimit} 枚）");
                match = next;
            }
        }

        /// <summary>ターンを終えて、相手のターンにする。新しいターンプレイヤーはルールの枚数を引く</summary>
        void EndTurn()
        {
            var q = !turn;
            var before = state.Get(q).Hand.Count;
            var next = match.Step(game.Rules, TChoice.EndTurn());
            if (next == null)
            {
                log.Add($"（できません）ターン終了：{EndTurnBlocked() ?? "今はできません"}");
                return;
            }
            match = next;
            blockPlan.Clear();
            log.Add($"── 第{turnCount}ターン：{Who(turn)}のターン ──");
            var drawn = state.Get(q).Hand.Count - before;
            if (game.Rules.DrawPerTurn > 0)
                log.Add(drawn == game.Rules.DrawPerTurn ? $"{Who(q)}：{drawn} 枚ドロー" : $"{Who(q)}：デッキが足りず {drawn} 枚だけ引きました（デッキ切れで負け）");
            judge.Sync(state, game.Rules, turn);
            ClearSelection();
        }

        static string Who(bool p) => p ? "自分" : "相手";

        /// <summary>両者が続けてパスする（デモと場面づくり用）</summary>
        void PassBoth()
        {
            for (int i = 0; i < 2 && match.Turn.Passes < 2; i++)
            {
                var next = match.Step(game.Rules, TChoice.Pass());
                if (next == null) break;
                log.Add($"{Who(match.Turn.Prio)}：パス");
                match = next;
            }
        }

        /// <summary>ゾーンの何番目のマスか（表示用。1 から数える）</summary>
        string CellName(int zi, int cell)
        {
            var z = game.Rules.Zones[zi];
            return z.Capacity == Capacity.One && z.Count > 1 ? $"{z.Name}の{cell + 1}番目のマス" : z.Name;
        }

        /// <summary>選んでいる手札を置く動き（ターンプレイヤーなら place、そうでなければインスタントの cast）</summary>
        TChoice PlaceChoice(bool p, int zi, int cell, List<string> pay) =>
            p == turn ? TChoice.Place(selHand, zi, cell, placeUp, pay) : TChoice.Cast(selHand, zi, cell, placeUp, pay);

        /// <summary>選んでいる手札を、ゾーン zi の cell 番目のマスに置けるか</summary>
        bool CanPlaceSelected(bool p, int zi, int cell) =>
            selHand >= 0 && selPlayer == p && selHand < state.Get(p).Hand.Count &&
            match.Step(game.Rules, PlaceChoice(p, zi, cell, SelectedPay(p))) != null;

        void Do(TChoice ch, string message)
        {
            var next = match.Step(game.Rules, ch);
            if (next == null) { log.Add($"（できません）{message}"); Render(); return; }
            match = next;
            if (ch.Kind == TChoiceKind.Block) blockPlan.Clear();
            targeting = null;
            log.Add(message);
            judge.Sync(state, game.Rules, turn);
            Settle();
            ClearSelection();
            Render();
        }

        /// <summary>
        /// 状態の確認：守備力以上のダメージを受けている（MTG 式の戦闘では守備力が 0 の）戦闘できるカードがあれば、
        /// 今の無効の状態で破壊する（ターンの終わりまでの変化や、守備力を上げる効果がなくなったときなど）
        /// </summary>
        void Settle()
        {
            var neg = NegList(NegationStatus(out _));
            var next = match.Step(game.Rules, TChoice.Settle(neg));
            if (next == null) return;
            var gone = new[] { true, false }.SelectMany(q => state.Get(q).Field
                .Where(x => !next.G.Get(q).Field.Any(y => y.Key == x.Key)).Select(x => $"{Who(q)}の{x.Card.Name}")).ToList();
            if (gone.Count == 0) return;
            match = next;
            log.Add($"状態の確認：{string.Join("・", gone)}を破壊（守備力以上のダメージ）");
            judge.Sync(state, game.Rules, turn);
        }

        /// <summary>対象を選ぶ範囲を持つ動きか</summary>
        static Selector TargetSel(Action a) => a switch
        {
            Destroy d when d.Target.Target => d.Target,
            Bounce b when b.Target.Target => b.Target,
            Strike s when s.Target.Target => s.Target,
            Pump pu when pu.Target.Target => pu.Target,
            Counter c when c.Target.Target => c.Target,
            _ => null,
        };

        /// <summary>p のフィールドの k 番目のカードの効果 act で、対象に選べるカードの位置（どれかの動きの範囲に合うもの）</summary>
        List<(bool, int)> TargetsFor(bool p, int k, Activated act)
        {
            var r = game.Rules;
            var me = state.Get(p).Field[k];
            var l = new List<(bool, int)>();
            foreach (var q in new[] { true, false })
            {
                var f = state.Get(q).Field;
                for (int i = 0; i < f.Count; i++)
                {
                    if (q == p && i == k) continue;
                    var sl = f[i];
                    var src = new Src(p, r.CellOf(p, me.Zone, me.Cell), (q, sl.Base()));
                    var hit = act.Actions.Any(a =>
                    {
                        var sel = TargetSel(a);
                        if (sel == null || !sel.Matches(sl.ViewFor(r, q, src))) return false;
                        return a is Counter ? !r.OnFieldZone(sl.Zone)
                            : a is Strike || a is Pump ? MatchState.Fights(r, sl) : r.OnFieldZone(sl.Zone);
                    });
                    if (hit) l.Add((q, i));
                }
            }
            return l;
        }

        /// <summary>発動する：対象を選ぶ範囲があれば、対象を選ぶ場面にする</summary>
        void StartResolve(bool p, int k, int e, bool apply, List<(bool, int)> negs, string message)
        {
            var act = (Activated)state.Get(p).Field[k].Card.Effects[e];
            if (apply && act.Actions.Any(a => TargetSel(a) != null)) { targeting = (p, k, e, message); Render(); return; }
            Do(TChoice.Resolve(p, k, e, apply, negs), message);
        }

        /// <summary>マナの色の表示名（"" は無色）</summary>
        static string ColorName(string c) => c == "" ? "無色" : c;

        /// <summary>マナの並びを「赤2・緑1」の形にする</summary>
        static string PoolText(List<string> pool) =>
            pool.Count == 0 ? "なし" : string.Join("・", pool.GroupBy(x => x).Select(g => $"{ColorName(g.Key)}{g.Count()}"));

        /// <summary>カードのコストの表示（例：「1＋緑」「赤赤」「0」）</summary>
        public static string CostText(Card c)
        {
            var colors = string.Concat(c.ColorCost);
            if (c.Cost == 0 && colors.Length == 0) return "0";
            if (colors.Length == 0) return c.Cost.ToString();
            return c.Cost == 0 ? colors : $"{c.Cost}＋{colors}";
        }

        /// <summary>タップで出るマナの表示（例：「赤マナ +1」「赤か緑のマナ +1」。color を選んだならその色）</summary>
        static string ManaText(Card c, string color = null) =>
            color != null && c.ManaChoice.Count > 0 ? $"{ColorName(color)}マナ +{c.Mana}"
            : c.ManaChoice.Count > 0 ? $"{string.Join("か", c.ManaChoice)}のマナ +{c.Mana}" : $"{ColorName(c.ManaColor)}マナ +{c.Mana}";

        /// <summary>p のマナ（ターンプレイヤーなら pool、そうでなければ相手のターンに出したマナ）</summary>
        List<string> PoolOf(bool p) => p == turn ? match.Turn.Pool : match.Turn.OppPool;

        static string PayText(List<string> pay) => pay.Count == 0 ? "" : $"（{PoolText(pay)} で払う）";

        /// <summary>選んでいる手札を置くときに払うマナ（自分で選んでいなければ自動の払い方。払えなければ空にして、置けない動きにする）</summary>
        List<string> SelectedPay(bool p) =>
            customPay != null ? customPay
            : selHand >= 0 && selHand < state.Get(p).Hand.Count
                ? TurnInfo.AutoPay(state.Get(p).Hand[selHand], PoolOf(p)) ?? new List<string>() : new List<string>();

        /// <summary>マナやタップを使うルールか（カードにコストかマナがあるか、攻撃でタップするか）</summary>
        bool UsesMana => game.Rules.AttackTaps || game.Cards.Any(c => c.Cost > 0 || c.ColorCost.Count > 0 || c.Mana > 0);

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
            if (!t.Quiet && !TurnInfo.Instant(r, sl.Card))
                return t.Attackers.Count > 0 ? "攻撃の途中なので、インスタントしか置けません" : "スタックにカードがあるので、インスタントしか置けません";
            if (TurnInfo.AutoPay(sl.Card, t.Pool) == null)
                return $"マナが足りません（コスト {CostText(sl.Card)}・今のマナ {PoolText(t.Pool)}）。マナを出すカードを選んでタップしてください";
            if (customPay != null && !TurnInfo.PayOK(sl.Card, t.Pool, customPay))
                return $"選んだマナ（{PoolText(customPay)}）では払えません（コスト {CostText(sl.Card)}）";
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
            Strike st => NodeView.SelectorSummary(st.Target).Replace("\n", "・") + $"に{st.Amount}ダメージ",
            Pump pu => NodeView.SelectorSummary(pu.Target).Replace("\n", "・") +
                       $"をターンの終わりまで {(pu.Attack >= 0 ? "+" : "")}{pu.Attack}/{(pu.Defense >= 0 ? "+" : "")}{pu.Defense}",
            Counter co => NodeView.SelectorSummary(co.Target).Replace("\n", "・") + "を打ち消す",
            _ => "",
        };

        /// <summary>勝敗（対戦が終わっていれば）</summary>
        string Winner()
        {
            if (!match.Over(game.Rules)) return null;
            if (match.Turn.Decked is bool d) return $"{Who(!d)}の勝ち（{Who(d)}がデッキから引けなかった）";
            var w = match.Winner(game.Rules);
            if (w == null) return "引き分け（お互いのライフが 0）";
            return $"{Who(w.Value)}の勝ち（{Who(!w.Value)}のライフが 0）";
        }
    }
}
