// ターンのある対戦（CardGen/Turn.lean と同じ意味）。
using System.Collections.Generic;
using System.Linq;

namespace CardGen
{
    /// <summary>ターンの情報（TurnInfo）。カードの記録はダメージを除いたもの（Slot.Base）で覚える</summary>
    public sealed class TurnInfo
    {
        /// <summary>ターンプレイヤー</summary>
        public bool Tp;
        /// <summary>何ターン目か（1 から）</summary>
        public int Count = 1;
        /// <summary>このターンに置いた、戦闘できる種類のカードの枚数</summary>
        public int Summons;
        /// <summary>このターンに攻撃したカード（ターンプレイヤーのフィールドにあるものだけ）</summary>
        public List<Slot> Attacked = new List<Slot>();
        /// <summary>このターンにターンプレイヤーが置いたカードの種類（置いた順）</summary>
        public List<string> Placed = new List<string>();
        /// <summary>このターンに置いたカード（ターンプレイヤーのフィールドにあるものだけ。召喚酔いに使う）</summary>
        public List<Slot> Entered = new List<Slot>();
        /// <summary>ターンプレイヤーのマナ（色の名前を1マナにつき1つ。"" は無色）</summary>
        public List<string> Pool = new List<string>();
        /// <summary>相手のマナ（インスタントを置くために、このターンにタップして出したもの）</summary>
        public List<string> OppPool = new List<string>();
        /// <summary>タップしている、ターンプレイヤーのカード</summary>
        public List<Slot> Tapped = new List<Slot>();
        /// <summary>タップしている、相手のカード</summary>
        public List<Slot> OppTapped = new List<Slot>();
        /// <summary>攻撃を宣言して、ブロックを待っているカード（宣言した順）。MTG 式の戦闘だけで使う</summary>
        public List<Slot> Attackers = new List<Slot>();
        /// <summary>このターンにブロックした、相手のカード</summary>
        public List<Slot> Blocked = new List<Slot>();
        /// <summary>スタック（一番上から順に、置いたプレイヤーとカード）</summary>
        public List<(bool player, Slot slot)> Stack = new List<(bool, Slot)>();
        /// <summary>このターンにタップで出したマナの合計（両方のプレイヤー）</summary>
        public int Made;
        /// <summary>このターンに払ったマナの合計（両方のプレイヤー）</summary>
        public int Spent;
        /// <summary>ターンの最初に引く枚数が足りずに負けたプレイヤー</summary>
        public bool? Decked;
        /// <summary>優先権を持つプレイヤー（公理：優先権を持つプレイヤーだけが動ける）。指定しなければターンプレイヤー</summary>
        public bool Prio { get => prio ?? Tp; set => prio = value; }
        bool? prio;
        /// <summary>続けてパスした回数（2 なら両者がパスした：スタックの一番上の解決か、ブロックを待つ）</summary>
        public int Passes;

        /// <summary>Lean の Slot.base の等しさ（ゾーン・マス・カード・表裏が同じ。ダメージは見ない）</summary>
        public static bool SameSlot(Slot a, Slot b) => a.SameBase(b);

        static int CountOf(IEnumerable<Slot> l, Slot s) => l.Count(x => SameSlot(x, s));

        /// <summary>prune：記録を、今のフィールドにあるものだけに絞る（同じカードはある枚数まで）</summary>
        public static List<Slot> Prune(List<Slot> record, List<Slot> field)
        {
            var rest = field.ToList();
            var result = new List<Slot>();
            foreach (var a in record)
            {
                int i = rest.FindIndex(x => SameSlot(x, a));
                if (i < 0) continue;
                result.Add(a);
                rest.RemoveAt(i);
            }
            return result;
        }

        /// <summary>pruneStack：スタックの記録を、今のフィールドにあるものだけに絞る</summary>
        public static List<(bool, Slot)> PruneStack(List<(bool player, Slot slot)> stack, MatchState g)
        {
            var rest = new Dictionary<bool, List<Slot>> { [true] = g.P1.Field.ToList(), [false] = g.P2.Field.ToList() };
            var result = new List<(bool, Slot)>();
            foreach (var (q, a) in stack)
            {
                int i = rest[q].FindIndex(x => SameSlot(x, a));
                if (i < 0) continue;
                result.Add((q, a));
                rest[q].RemoveAt(i);
            }
            return result;
        }

        /// <summary>notIn：記録 l にない（同じカードのうち、記録にない1枚がフィールドにある）</summary>
        public static bool NotIn(List<Slot> l, List<Slot> field, Slot sl) => CountOf(l, sl) < CountOf(field, sl);

        public TurnInfo Copy() => new TurnInfo
        {
            Tp = Tp, Count = Count, Summons = Summons, Attacked = Attacked.ToList(), Placed = Placed.ToList(),
            Entered = Entered.ToList(), Pool = Pool.ToList(), OppPool = OppPool.ToList(), Tapped = Tapped.ToList(),
            OppTapped = OppTapped.ToList(), Attackers = Attackers.ToList(), Blocked = Blocked.ToList(),
            Stack = Stack.ToList(), Made = Made, Spent = Spent, Decked = Decked, prio = prio, Passes = Passes,
        };

        TurnInfo WithPrio(bool p, int n) { var t = Copy(); t.Prio = p; t.Passes = n; return t; }

        /// <summary>TurnInfo.afterPasses：両者が続けてパスしたあとにだけできる動きか（スタックの一番上の解決と、ブロック）</summary>
        public bool AfterPasses(Rules r, TChoice ch) =>
            ch.Kind == TChoiceKind.Block || (ch.Kind == TChoiceKind.Resolve && r.Stack && Stack.Count > 0);

        /// <summary>TurnInfo.prioOK：優先権について、その動きをしてよいか</summary>
        public bool PrioOK(Rules r, TChoice ch) =>
            ch.Kind == TChoiceKind.Settle ||
            (AfterPasses(r, ch) ? Passes == 2 : Passes < 2 && ch.Actor(Tp) == Prio);

        /// <summary>TurnInfo.afterPass：パスしたあと（両者がパスしても、何もなければターンプレイヤーに戻る）</summary>
        public TurnInfo AfterPass() =>
            Passes + 1 < 2 ? WithPrio(!Prio, Passes + 1) : Quiet ? WithPrio(Tp, 0) : WithPrio(!Prio, 2);

        /// <summary>TurnInfo.prioAfter：動いたあとの優先権</summary>
        public TurnInfo PrioAfter(Rules r, TurnInfo after, TChoice ch) =>
            ch.Kind == TChoiceKind.Settle ? after.WithPrio(Prio, Passes)
            : ch.Kind == TChoiceKind.EndTurn ? after.WithPrio(after.Tp, 0)
            : AfterPasses(r, ch) ? after.WithPrio(after.Tp, 0) : after.WithPrio(ch.Actor(Tp), 0);

        /// <summary>TurnInfo.prune：記録を新しい盤面に合わせる</summary>
        public TurnInfo Pruned(MatchState g)
        {
            var t = Copy();
            var mine = g.Get(Tp).Field;
            var opp = g.Get(!Tp).Field;
            t.Attacked = Prune(Attacked, mine);
            t.Entered = Prune(Entered, mine);
            t.Tapped = Prune(Tapped, mine);
            t.OppTapped = Prune(OppTapped, opp);
            t.Attackers = Prune(Attackers, mine);
            t.Blocked = Prune(Blocked, opp);
            t.Stack = PruneStack(Stack, g);
            return t;
        }

        /// <summary>このカードはこのターンにまだ攻撃していないか</summary>
        public bool CanAttack(Slot sl, List<Slot> field) => NotIn(Attacked, field, sl);

        /// <summary>bagLeB：l の各要素の個数が m の個数以下</summary>
        public static bool BagLe(List<string> l, List<string> m) => l.All(a => l.Count(x => x == a) <= m.Count(x => x == a));

        /// <summary>payOK：マナ pay でカード c のコストを払えるか</summary>
        public static bool PayOK(Card c, List<string> pool, List<string> pay) =>
            BagLe(pay, pool) && BagLe(c.ColorCost, pay) && pay.Count == c.Cost + c.ColorCost.Count;

        /// <summary>autoPay：払い方を1つ選ぶ（色の決まったコストはその色、残りは無色から先に、次に持っている順）。払えなければ null</summary>
        public static List<string> AutoPay(Card c, List<string> pool)
        {
            var rest = pool.ToList();
            foreach (var col in c.ColorCost) rest.Remove(col);
            var generic = rest.Where(x => x == "").Concat(rest.Where(x => x != "")).ToList();
            var pay = c.ColorCost.Concat(generic.Take(c.Cost)).ToList();
            return PayOK(c, pool, pay) ? pay : null;
        }

        /// <summary>TurnInfo.quiet：攻撃の途中でも、スタックが空でなくてもない</summary>
        public bool Quiet => Attackers.Count == 0 && Stack.Count == 0;

        /// <summary>Rules.instant：いつでも置ける種類のカードか</summary>
        public static bool Instant(Rules r, Card c) => r.Instants.Contains(c.Type);

        /// <summary>Rules.spell：置くとスタックに積まれるか</summary>
        public static bool Spell(Rules r, Slot sl) => r.Stack && !r.OnFieldZone(sl.Zone) && sl.Card.Effects.Any(e => e is Activated);

        /// <summary>TurnInfo.placeOK：ターンプレイヤーが、マナ pay で払って置けるか（置ける時か・召喚の上限・種類ごとの上限・マナ）</summary>
        public bool PlaceOK(Rules r, Slot sl, List<string> pay) =>
            (Quiet || Instant(r, sl.Card)) &&
            (!MatchState.Fights(r, sl) || r.SummonsPerTurn == 0 || Summons < r.SummonsPerTurn) &&
            r.PlaceLimits.All(l => !l.Types.Contains(sl.Card.Type) || Placed.Count(l.Types.Contains) < l.Count) &&
            PayOK(sl.Card, Pool, pay);

        /// <summary>TurnInfo.castOK：ターンプレイヤーでない方が、インスタントをマナ pay で払って置けるか</summary>
        public bool CastOK(Rules r, Slot sl, List<string> pay) => Instant(r, sl.Card) && PayOK(sl.Card, OppPool, pay);

        /// <summary>TurnInfo.sick：召喚酔いで動けないか</summary>
        public bool Sick(Rules r, List<Slot> field, Slot sl) =>
            r.SummoningSickness && MatchState.Fights(r, sl) && !NotIn(Entered, field, sl);

        /// <summary>TurnInfo.attackOK：このターンに攻撃できるか（スタックが空のときだけ）</summary>
        public bool AttackOK(Rules r, List<Slot> field, Slot sl) =>
            Stack.Count == 0 && (r.FirstTurnAttack || Count != 1) && NotIn(Attacked, field, sl) &&
            (!r.AttackTaps || NotIn(Tapped, field, sl)) && !Sick(r, field, sl);

        /// <summary>manaOut：タップして出るマナ（color：2色以上から選べるときの色。選べない色なら null）</summary>
        public static List<string> ManaOut(Card c, string color)
        {
            if (c.ManaChoice.Count == 0) return Enumerable.Repeat(c.ManaColor, c.Mana).ToList();
            return c.ManaChoice.Contains(color) ? Enumerable.Repeat(color, c.Mana).ToList() : null;
        }

        /// <summary>TurnInfo.tapOK：ターンプレイヤーがタップしてマナを出せるか</summary>
        public bool TapOK(Rules r, List<Slot> field, Slot sl) =>
            sl.FaceUp && r.OnFieldZone(sl.Zone) && sl.Card.Mana > 0 && NotIn(Tapped, field, sl) && !Sick(r, field, sl);

        /// <summary>TurnInfo.oppTapOK：ターンプレイヤーでない方がタップしてマナを出せるか</summary>
        public bool OppTapOK(Rules r, List<Slot> field, Slot sl) =>
            sl.FaceUp && r.OnFieldZone(sl.Zone) && sl.Card.Mana > 0 && NotIn(OppTapped, field, sl);

        /// <summary>blockers：ブロックに選んだ相手のカード（ダメージを除いたもの）</summary>
        public static List<Slot> Blockers(List<Slot> opp, List<(int j, int a)> blocks) =>
            blocks.Where(b => b.j >= 0 && b.j < opp.Count).Select(b => opp[b.j].Base()).ToList();

        /// <summary>TurnInfo.blockOK：相手のフィールド opp のカードでブロックを選べるか</summary>
        public bool BlockOK(Rules r, List<Slot> opp, List<(int j, int a)> blocks)
        {
            var bs = Blockers(opp, blocks);
            var js = blocks.Select(b => b.j).ToList();
            return Stack.Count == 0 && Attackers.Count > 0 && js.Distinct().Count() == js.Count && bs.Count == blocks.Count &&
                   blocks.All(b => b.a >= 0 && b.a < Attackers.Count) &&
                   bs.All(b => CountOf(bs, b) + CountOf(Blocked, b) <= CountOf(opp, b) &&
                               (!r.AttackTaps || CountOf(bs, b) + CountOf(OppTapped, b) <= CountOf(opp, b))) &&
                   blocks.All(b => !Attackers[b.a].Card.Flying || opp[b.j].Card.Flying || opp[b.j].Card.Reach);
        }

        /// <summary>locate：記録のカードの、フィールドでの位置（同じカードが複数あれば、まだ選んでいない前のものから）</summary>
        public static List<int> Locate(List<Slot> field, List<Slot> rec)
        {
            var used = new List<int>();
            foreach (var a in rec)
            {
                var i = Enumerable.Range(0, field.Count).Where(x => SameSlot(field[x], a) && !used.Contains(x)).DefaultIfEmpty(-1).First();
                if (i >= 0) used.Add(i);
            }
            return used;
        }

        /// <summary>TurnInfo.topOK：スタックの一番上が、p のフィールドの k 番目のカードか（スタックが空か、スタックのルールがなければ、どれでもよい）</summary>
        public bool TopOK(Rules r, MatchState g, bool p, int k)
        {
            if (!r.Stack || Stack.Count == 0) return true;
            var (q, top) = Stack[0];
            var f = g.Get(p).Field;
            return q == p && k >= 0 && k < f.Count && SameSlot(f[k], top);
        }

        /// <summary>タップしているか（どちらのプレイヤーのカードでも）</summary>
        public bool IsTapped(bool owner, List<Slot> field, Slot sl) =>
            !NotIn(owner == Tp ? Tapped : OppTapped, field, sl);
    }

    public enum TChoiceKind { Place, Cast, Resolve, Attack, Block, Tap, OppTap, EndTurn, Settle, Pass }

    /// <summary>ターンのある対戦の動き（TChoice）</summary>
    public sealed class TChoice
    {
        public TChoiceKind Kind;
        /// <summary>発動するプレイヤー（Resolve のみ）</summary>
        public bool Player;
        public int Hand, Zone, Cell, Field, Effect;
        public bool FaceUp, Apply;
        public int? Target;
        public List<(bool player, int index)> Neg = new List<(bool, int)>();
        /// <summary>置くときに払うマナ</summary>
        public List<string> Pay = new List<string>();
        /// <summary>タップするときに選ぶマナの色</summary>
        public string Color = "";
        /// <summary>ブロック：(ブロックするカードの位置, 何番目に宣言された攻撃をブロックするか)</summary>
        public List<(int blocker, int attacker)> Blocks = new List<(int, int)>();
        /// <summary>解決するときに選んだ対象の位置</summary>
        public (bool player, int index)? Tgt;

        public static TChoice Place(int hand, int zone, int cell, bool faceUp, List<string> pay = null) =>
            new TChoice { Kind = TChoiceKind.Place, Hand = hand, Zone = zone, Cell = cell, FaceUp = faceUp,
                          Pay = pay ?? new List<string>() };
        public static TChoice Cast(int hand, int zone, int cell, bool faceUp, List<string> pay = null) =>
            new TChoice { Kind = TChoiceKind.Cast, Hand = hand, Zone = zone, Cell = cell, FaceUp = faceUp,
                          Pay = pay ?? new List<string>() };
        public static TChoice Resolve(bool p, int field, int effect, bool apply, List<(bool, int)> neg = null,
            (bool, int)? tgt = null) =>
            new TChoice { Kind = TChoiceKind.Resolve, Player = p, Field = field, Effect = effect, Apply = apply,
                          Neg = neg ?? new List<(bool, int)>(), Tgt = tgt };
        public static TChoice Settle(List<(bool, int)> neg) => new TChoice { Kind = TChoiceKind.Settle, Neg = neg };
        public static TChoice Pass() => new TChoice { Kind = TChoiceKind.Pass };

        /// <summary>TChoice.actor：動きをするプレイヤー</summary>
        public bool Actor(bool tp) => Kind switch
        {
            TChoiceKind.Cast => !tp,
            TChoiceKind.OppTap => !tp,
            TChoiceKind.Block => !tp,
            TChoiceKind.Resolve => Player,
            _ => tp,
        };
        public static TChoice Attack(int field, int? target, List<(bool, int)> neg) =>
            new TChoice { Kind = TChoiceKind.Attack, Field = field, Target = target, Neg = neg };
        public static TChoice Block(List<(int, int)> blocks, List<(bool, int)> neg) =>
            new TChoice { Kind = TChoiceKind.Block, Blocks = blocks, Neg = neg };
        public static TChoice Tap(int field, string color = "") => new TChoice { Kind = TChoiceKind.Tap, Field = field, Color = color };
        public static TChoice OppTap(int field, string color = "") =>
            new TChoice { Kind = TChoiceKind.OppTap, Field = field, Color = color };
        public static TChoice EndTurn() => new TChoice { Kind = TChoiceKind.EndTurn };
    }

    /// <summary>ターンのある対戦の状態（Match）：盤面とターンの情報</summary>
    public sealed class Match
    {
        public MatchState G;
        public TurnInfo Turn;

        /// <summary>drawUpTo：n 枚引く（デッキが足りなければある分だけ）</summary>
        public static MatchState DrawUpTo(Rules r, bool p, int n, MatchState g)
        {
            for (int k = 0; k < n; k++)
            {
                var next = g.Step(r, Choice.Draw(p));
                if (next == null) break;
                g = next;
            }
            return g;
        }

        /// <summary>Match.start：開始時の状態（first が先攻）</summary>
        public static Match Start(Rules r, List<Card> deck1, List<Card> deck2, bool first)
        {
            var g = MatchState.Start(r, deck1, deck2);
            if (r.FirstTurnDraw) g = DrawUpTo(r, first, r.DrawPerTurn, g);
            return new Match { G = g, Turn = new TurnInfo { Tp = first, Prio = first } };
        }

        /// <summary>Match.over：対戦が終わっているか（デッキ切れか、ライフのルールでどちらかのライフが 0）</summary>
        public bool Over(Rules r) => Turn.Decked != null || (r.Life > 0 && (G.P1.Life == 0 || G.P2.Life == 0));

        /// <summary>勝ったプレイヤー（対戦が終わっていないか、両方のライフが 0 なら null）</summary>
        public bool? Winner(Rules r)
        {
            if (Turn.Decked is bool d) return !d;
            if (r.Life > 0 && G.P1.Life == 0 && G.P2.Life > 0) return false;
            if (r.Life > 0 && G.P2.Life == 0 && G.P1.Life > 0) return true;
            return null;
        }

        Match Next(MatchState g, TurnInfo t) => new Match { G = g, Turn = t.Pruned(g) };

        /// <summary>Match.step?：選んだ動きをしたあとの状態（できない動きなら null）。優先権を持つプレイヤーだけが動ける</summary>
        public Match Step(Rules r, TChoice ch)
        {
            if (Over(r)) return null;
            if (ch.Kind == TChoiceKind.Pass)
                return Turn.Passes < 2 ? new Match { G = G, Turn = Turn.AfterPass() } : null;
            if (!Turn.PrioOK(r, ch)) return null;
            var m = Step0(r, ch);
            return m == null ? null : new Match { G = m.G, Turn = Turn.PrioAfter(r, m.Turn, ch) };
        }

        /// <summary>Match.step0?：優先権を考えない1歩</summary>
        Match Step0(Rules r, TChoice ch)
        {
            var p = Turn.Tp;
            switch (ch.Kind)
            {
                case TChoiceKind.Place:
                case TChoiceKind.Cast:
                {
                    var place = ch.Kind == TChoiceKind.Place;
                    var who = place ? p : !p;
                    var hand = G.Get(who).Hand;
                    if (ch.Hand < 0 || ch.Hand >= hand.Count) return null;
                    var sl = new Slot(ch.Zone, ch.Cell, hand[ch.Hand], ch.FaceUp);
                    if (place ? !Turn.PlaceOK(r, sl, ch.Pay) : !Turn.CastOK(r, sl, ch.Pay)) return null;
                    var g = G.Step(r, Choice.Place(who, ch.Hand, ch.Zone, ch.Cell, ch.FaceUp));
                    if (g == null) return null;
                    var t = Turn.Copy();
                    if (place)
                    {
                        t.Summons += MatchState.Fights(r, sl) ? 1 : 0;
                        t.Placed.Add(sl.Card.Type);
                        t.Entered.Insert(0, sl);
                        foreach (var x in ch.Pay) t.Pool.Remove(x);
                    }
                    else foreach (var x in ch.Pay) t.OppPool.Remove(x);
                    t.Spent += ch.Pay.Count;
                    if (TurnInfo.Spell(r, sl)) t.Stack.Insert(0, (who, sl));
                    return Next(g, t);
                }
                case TChoiceKind.Resolve:
                {
                    if (!Turn.TopOK(r, G, ch.Player, ch.Field)) return null;
                    var g = G.Step(r, Choice.Resolve(ch.Player, ch.Field, ch.Effect, ch.Apply, ch.Neg, ch.Tgt));
                    if (g == null) return null;
                    var t = Turn.Copy();
                    if (r.Stack && t.Stack.Count > 0) t.Stack.RemoveAt(0);
                    return Next(g, t);
                }
                case TChoiceKind.Attack:
                {
                    var field = G.Get(p).Field;
                    if (ch.Field < 0 || ch.Field >= field.Count) return null;
                    var sl = field[ch.Field];
                    if (!Turn.AttackOK(r, field, sl)) return null;
                    var t = Turn.Copy();
                    t.Attacked.Insert(0, sl.Base());
                    if (r.AttackTaps) t.Tapped.Insert(0, sl.Base());
                    if (r.Blocking)
                    {
                        // 攻撃の宣言：相手がブロックを選ぶまで待つ
                        if (!(sl.FaceUp && MatchState.Fights(r, sl) && ch.Target == null)) return null;
                        t.Attackers.Add(sl.Base());
                        return Next(G, t);
                    }
                    if (!Turn.Quiet) return null;
                    var g = G.Step(r, Choice.Attack(p, ch.Field, ch.Target, ch.Neg));
                    if (g == null) return null;
                    return Next(g, t);
                }
                case TChoiceKind.Block:
                {
                    var opp = G.Get(!p).Field;
                    if (!Turn.BlockOK(r, opp, ch.Blocks)) return null;
                    var atk = TurnInfo.Locate(G.Get(p).Field, Turn.Attackers);
                    var g = G.Step(r, Choice.Combat(p, atk, ch.Blocks, ch.Neg));
                    if (g == null) return null;
                    var t = Turn.Copy();
                    t.Attackers.Clear();
                    t.Blocked.InsertRange(0, TurnInfo.Blockers(opp, ch.Blocks));
                    return Next(g, t);
                }
                case TChoiceKind.Tap:
                case TChoiceKind.OppTap:
                {
                    var mine = ch.Kind == TChoiceKind.Tap;
                    var field = G.Get(mine ? p : !p).Field;
                    if (ch.Field < 0 || ch.Field >= field.Count) return null;
                    var sl = field[ch.Field];
                    var o = TurnInfo.ManaOut(sl.Card, ch.Color);
                    if (o == null) return null;
                    if (mine ? !Turn.TapOK(r, field, sl) : !Turn.OppTapOK(r, field, sl)) return null;
                    var t = Turn.Copy();
                    if (mine) { t.Pool.AddRange(o); t.Tapped.Insert(0, sl.Base()); }
                    else { t.OppPool.AddRange(o); t.OppTapped.Insert(0, sl.Base()); }
                    t.Made += o.Count;
                    return Next(G, t);
                }
                case TChoiceKind.Settle:
                {
                    var g = G.Sweep(r, ch.Neg);
                    return Next(g, Turn);
                }
                default:
                {
                    if (!Turn.Quiet) return null;
                    var g1 = G.Mend();
                    var g = DrawUpTo(r, !p, r.DrawPerTurn, g1);
                    var t = new TurnInfo { Tp = !p, Prio = !p, Count = Turn.Count + 1, OppTapped = Turn.Tapped.ToList() };
                    if (g1.Get(!p).Deck.Count < r.DrawPerTurn) t.Decked = !p;
                    return Next(g, t);
                }
            }
        }

        /// <summary>このターンにこのカードを置けるか（置ける時か・召喚の上限・種類ごとの上限・マナ。置ける場所は MatchState.Step が決める）</summary>
        public bool SummonOK(Rules r, Slot sl, List<string> pay) => Turn.PlaceOK(r, sl, pay);

        /// <summary>このターンに攻撃できる時期か（先攻の最初のターンでないか、ルールで許されているか）</summary>
        public bool AttackPhaseOK(Rules r) => r.FirstTurnAttack || Turn.Count != 1;
    }
}
