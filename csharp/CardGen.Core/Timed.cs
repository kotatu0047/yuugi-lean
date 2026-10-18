// 適用の時刻つきの判定（CardGen/Timed.lean と同じ意味）。
using System.Collections.Generic;
using System.Linq;

namespace CardGen
{
    /// <summary>TState：カードごとの有効・無効と、カードの番号を適用の時刻の古い順に並べた列</summary>
    public sealed class TState
    {
        public readonly bool[] On;
        public readonly int[] Order;
        public TState(bool[] on, int[] order) { On = on; Order = order; }

        public bool IsOn(int i) => i >= 0 && i < On.Length && On[i];

        /// <summary>適用の時刻（小さいほど古い）。列にない番号は列の長さ（Lean の List.idxOf と同じ）</summary>
        public int Time(int i)
        {
            int k = System.Array.IndexOf(Order, i);
            return k < 0 ? Order.Length : k;
        }

        public TState Kill(int i)
        {
            var on = (bool[])On.Clone();
            if (i >= 0 && i < on.Length) on[i] = false;
            return new TState(on, Order);
        }

        /// <summary>有効に戻して、時刻を一番新しくする</summary>
        public TState Revive(int i)
        {
            var on = (bool[])On.Clone();
            if (i >= 0 && i < on.Length) on[i] = true;
            var order = Order.ToList();
            order.Remove(i);
            order.Add(i);
            return new TState(on, order.ToArray());
        }

        public string Key => string.Concat(On.Select(b => b ? '1' : '0')) + ":" + string.Join(",", Order);
    }

    /// <summary>TSys：無効の関係とカードのコントローラー</summary>
    public sealed class TSys
    {
        public readonly int N;
        readonly bool[,] rel;
        readonly bool[] ctrl;

        public TSys(IReadOnlyList<Inst> insts)
        {
            N = insts.Count;
            rel = new bool[N, N];
            for (int y = 0; y < N; y++)
                for (int x = 0; x < N; x++)
                    rel[y, x] = Negation.InstRel(insts, y, x);
            ctrl = insts.Select(i => i.Controller).ToArray();
        }

        public bool Rel(int y, int x) => rel[y, x];
        public bool Ctrl(int i) => ctrl[i];

        /// <summary>y が x に勝つ：y は x を無効にし、x が y を無効にして先に適用されている、ということはない</summary>
        public bool Beats(TState s, int y, int x) => rel[y, x] && !(rel[x, y] && s.Time(x) < s.Time(y));

        /// <summary>x が、適用中のカードのどれかに負けている</summary>
        public bool Beaten(TState s, int x) => Enumerable.Range(0, N).Any(y => s.IsOn(y) && Beats(s, y, x));

        /// <summary>何も無効にしないカード</summary>
        public bool Inert(int j) => !Enumerable.Range(0, N).Any(x => rel[j, x]);

        /// <summary>有効に戻すカードの候補（tp はターンプレイヤー）</summary>
        public List<int> Cands(TState s, bool tp)
        {
            var all = Enumerable.Range(0, N).Where(j => !s.IsOn(j) && !Beaten(s, j)).ToList();
            foreach (var j in all) if (Inert(j)) return new List<int> { j };
            var mine = all.Where(j => ctrl[j] == tp).ToList();
            return mine.Count == 0 ? all : mine;
        }

        /// <summary>負けている有効なカード（無効にする候補）</summary>
        public List<int> Losing(TState s) => Enumerable.Range(0, N).Where(i => s.IsOn(i) && Beaten(s, i)).ToList();

        /// <summary>判定の1歩で進める先（空なら止まる）</summary>
        public List<TState> Succ(bool tp, TState s)
        {
            var losing = Losing(s);
            return losing.Count == 0 ? Cands(s, tp).Select(s.Revive).ToList() : losing.Select(s.Kill).ToList();
        }

        /// <summary>ある状態から先の判定の見通し</summary>
        public sealed class Outlook
        {
            /// <summary>止まる状態（行き着けるものすべて）</summary>
            public List<TState> Ends = new List<TState>();
            /// <summary>選び方によって回り続けることがある</summary>
            public bool MayLoop;
            /// <summary>状態が多すぎて調べきれなかった</summary>
            public bool TooMany;
            /// <summary>どう選んでも止まり、結果は1通り</summary>
            public bool Unique => !TooMany && !MayLoop && Ends.Count == 1;
        }

        /// <summary>s から行き着ける状態をすべて調べる</summary>
        public Outlook Explore(bool tp, TState s, int maxStates = 20000)
        {
            var o = new Outlook();
            var succ = new Dictionary<string, List<TState>>();
            var stack = new Stack<TState>();
            stack.Push(s);
            while (stack.Count > 0)
            {
                var t = stack.Pop();
                if (succ.ContainsKey(t.Key)) continue;
                if (succ.Count >= maxStates) { o.TooMany = true; return o; }
                var next = Succ(tp, t);
                succ[t.Key] = next;
                if (next.Count == 0) o.Ends.Add(t);
                foreach (var u in next) stack.Push(u);
            }
            // 回り続けることがあるか：止まる状態へ必ず行き着く状態を、後ろから求める
            var allEnd = new HashSet<string>(o.Ends.Select(t => t.Key));
            for (var changed = true; changed;)
            {
                changed = false;
                foreach (var kv in succ)
                    if (!allEnd.Contains(kv.Key) && kv.Value.All(u => allEnd.Contains(u.Key))) { allEnd.Add(kv.Key); changed = true; }
            }
            o.MayLoop = !allEnd.Contains(s.Key);
            return o;
        }
    }

    /// <summary>
    /// 対戦中の無効の判定。フィールドのカード（盤面が進んでも同じ Slot オブジェクト）ごとに、有効・無効と
    /// 適用の時刻の順番を覚えておき、盤面が変わるたびに OCG の手順（TSys.Succ）で判定を進める。
    /// </summary>
    public sealed class Judge
    {
        public enum Outcome
        {
            /// <summary>どう選んでも結果は1通りで、そこまで進めた</summary>
            Unique,
            /// <summary>選んだ結果、判定が止まった</summary>
            Done,
            /// <summary>同じ状態に戻った（判定が止まらない）</summary>
            Loop,
            /// <summary>プレイヤーが選ぶ場面で止まっている（Choices）</summary>
            Choosing,
        }

        readonly Dictionary<Slot, bool> on = new Dictionary<Slot, bool>();
        readonly List<Slot> order = new List<Slot>();
        List<(bool player, int index, Slot slot, Inst inst)> cards = new List<(bool, int, Slot, Inst)>();
        TSys sys = new TSys(new List<Inst>());

        public Outcome Result { get; private set; } = Outcome.Unique;
        /// <summary>ターンプレイヤー</summary>
        public bool Turn { get; private set; } = true;
        /// <summary>選ぶ場面の選択肢：進む先と、有効・無効が変わるカード</summary>
        public List<(TState next, (bool player, int index, Slot slot) card)> Choices { get; private set; }
        /// <summary>選ぶ場面が「無効にする順番」か（そうでなければ「有効に戻す順番」）</summary>
        public bool ChoosingKill { get; private set; }
        /// <summary>選ぶ場面での見通し</summary>
        public TSys.Outlook Outlook { get; private set; }

        public bool IsOn(Slot sl) => on.TryGetValue(sl, out var b) && b;

        /// <summary>
        /// 盤面が変わったあとに判定を進める（tp はターンプレイヤー）。
        /// フィールドを離れたカードは忘れ、新しく置かれたカードは「まだ適用されていない（無効）」として、時刻の一番新しい側に加える。
        /// </summary>
        public void Sync(MatchState state, Rules r, bool tp)
        {
            Turn = tp;
            cards = state.FieldInsts(r).Select(x => (x.player, x.index, state.Get(x.player).Field[x.index], x.inst)).ToList();
            var present = new HashSet<Slot>(cards.Select(c => c.Item3));
            foreach (var sl in on.Keys.Where(sl => !present.Contains(sl)).ToList()) on.Remove(sl);
            order.RemoveAll(sl => !present.Contains(sl));
            foreach (var c in cards)
                if (!on.ContainsKey(c.Item3)) { on[c.Item3] = false; order.Add(c.Item3); }
            sys = new TSys(cards.Select(c => c.Item4).ToList());
            var index = new Dictionary<Slot, int>();
            for (int i = 0; i < cards.Count; i++) index[cards[i].Item3] = i;
            Advance(new TState(cards.Select(c => on[c.Item3]).ToArray(), order.Select(sl => index[sl]).ToArray()));
        }

        /// <summary>選ぶ場面で、選択肢の1つを選ぶ</summary>
        public void Choose(int k) => Advance(Choices[k].next);

        /// <summary>
        /// どう選んでも結果が1通りなら、そこまで進める。そうでなければ選択肢が1つの間は進め、選ぶ場面で止める。
        /// </summary>
        void Advance(TState s)
        {
            Choices = null;
            Outlook = sys.Explore(Turn, s);
            if (Outlook.Unique) { s = Outlook.Ends[0]; Result = Outcome.Unique; }
            else
            {
                var seen = new HashSet<string>();
                while (true)
                {
                    if (!seen.Add(s.Key)) { Result = Outcome.Loop; break; }
                    var next = sys.Succ(Turn, s);
                    if (next.Count == 0) { Result = Outcome.Done; break; }
                    if (next.Count == 1) { s = next[0]; continue; }
                    Result = Outcome.Choosing;
                    ChoosingKill = sys.Losing(s).Count > 0;
                    var cur = s;
                    Choices = next.Select(t =>
                    {
                        var c = cards[Enumerable.Range(0, sys.N).First(k => t.On[k] != cur.On[k])];
                        return (t, (c.player, c.index, c.slot));
                    }).ToList();
                    break;
                }
            }
            for (int i = 0; i < cards.Count; i++) on[cards[i].slot] = s.On[i];
            order.Clear();
            order.AddRange(s.Order.Select(i => cards[i].slot));
        }
    }
}
