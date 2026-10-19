// ターンのある対戦（CardGen/Turn.lean と同じ意味）。
using System.Collections.Generic;
using System.Linq;

namespace CardGen
{
    /// <summary>ターンの情報（TurnInfo）</summary>
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
        /// <summary>このターンに置いたカードの種類（置いた順）</summary>
        public List<string> Placed = new List<string>();
        /// <summary>このターンに置いたカード（ターンプレイヤーのフィールドにあるものだけ。召喚酔いに使う）</summary>
        public List<Slot> Entered = new List<Slot>();
        /// <summary>ターンプレイヤーのマナ（色の名前を1マナにつき1つ。"" は無色）</summary>
        public List<string> Pool = new List<string>();
        /// <summary>タップしている、ターンプレイヤーのカード</summary>
        public List<Slot> Tapped = new List<Slot>();
        /// <summary>タップしている、相手のカード</summary>
        public List<Slot> OppTapped = new List<Slot>();
        /// <summary>ブロックを待っている攻撃（攻撃したカードの、ターンプレイヤーのフィールドの位置）。MTG 式の戦闘だけで使う</summary>
        public int? Pending;
        /// <summary>このターンにブロックした、相手のカード</summary>
        public List<Slot> Blocked = new List<Slot>();

        /// <summary>Lean の Slot の等しさ（ゾーン・マス・カード・表裏が同じ）</summary>
        public static bool SameSlot(Slot a, Slot b) =>
            a.Zone == b.Zone && a.Cell == b.Cell && a.Card.Name == b.Card.Name && a.FaceUp == b.FaceUp;

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

        /// <summary>notIn：記録 l にない（同じカードのうち、記録にない1枚がフィールドにある）</summary>
        public static bool NotIn(List<Slot> l, List<Slot> field, Slot sl) => CountOf(l, sl) < CountOf(field, sl);

        public TurnInfo Copy() => new TurnInfo
        {
            Tp = Tp, Count = Count, Summons = Summons, Attacked = Attacked.ToList(), Placed = Placed.ToList(),
            Entered = Entered.ToList(), Pool = Pool.ToList(), Tapped = Tapped.ToList(), OppTapped = OppTapped.ToList(),
            Pending = Pending, Blocked = Blocked.ToList(),
        };

        /// <summary>TurnInfo.prune：記録を新しい盤面に合わせる</summary>
        public TurnInfo Pruned(MatchState g)
        {
            var t = Copy();
            var mine = g.Get(Tp).Field;
            t.Attacked = Prune(Attacked, mine);
            t.Entered = Prune(Entered, mine);
            t.Tapped = Prune(Tapped, mine);
            t.OppTapped = Prune(OppTapped, g.Get(!Tp).Field);
            t.Blocked = Prune(Blocked, g.Get(!Tp).Field);
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

        /// <summary>TurnInfo.placeOK：このターンに、マナ pay で払って置けるか（召喚の上限・種類ごとの上限・マナ）</summary>
        public bool PlaceOK(Rules r, Slot sl, List<string> pay) =>
            (!MatchState.Fights(r, sl) || r.SummonsPerTurn == 0 || Summons < r.SummonsPerTurn) &&
            r.PlaceLimits.All(l => !l.Types.Contains(sl.Card.Type) || Placed.Count(l.Types.Contains) < l.Count) &&
            PayOK(sl.Card, Pool, pay);

        /// <summary>TurnInfo.sick：召喚酔いで動けないか</summary>
        public bool Sick(Rules r, List<Slot> field, Slot sl) =>
            r.SummoningSickness && MatchState.Fights(r, sl) && !NotIn(Entered, field, sl);

        /// <summary>TurnInfo.attackOK：このターンに攻撃できるか</summary>
        public bool AttackOK(Rules r, List<Slot> field, Slot sl) =>
            (r.FirstTurnAttack || Count != 1) && NotIn(Attacked, field, sl) &&
            (!r.AttackTaps || NotIn(Tapped, field, sl)) && !Sick(r, field, sl);

        /// <summary>TurnInfo.tapOK：タップしてマナを出せるか</summary>
        public bool TapOK(Rules r, List<Slot> field, Slot sl) =>
            sl.FaceUp && r.OnFieldZone(sl.Zone) && sl.Card.Mana > 0 && NotIn(Tapped, field, sl) && !Sick(r, field, sl);

        /// <summary>TurnInfo.blockOK：相手のフィールド opp の target 番目のカードでブロックできるか</summary>
        public bool BlockOK(Rules r, List<Slot> opp, int? target)
        {
            if (target == null) return true;
            var j = target.Value;
            if (j < 0 || j >= opp.Count) return false;
            var tl = opp[j];
            return NotIn(Blocked, opp, tl) && (!r.AttackTaps || NotIn(OppTapped, opp, tl));
        }

        /// <summary>タップしているか（どちらのプレイヤーのカードでも）</summary>
        public bool IsTapped(bool owner, List<Slot> field, Slot sl) =>
            !NotIn(owner == Tp ? Tapped : OppTapped, field, sl);
    }

    public enum TChoiceKind { Place, Resolve, Attack, Block, Tap, EndTurn }

    /// <summary>ターンのある対戦の動き（TChoice）</summary>
    public sealed class TChoice
    {
        public TChoiceKind Kind;
        /// <summary>発動するプレイヤー（Resolve のみ。ほかはターンプレイヤー）</summary>
        public bool Player;
        public int Hand, Zone, Cell, Field, Effect;
        public bool FaceUp, Apply;
        public int? Target;
        public List<(bool player, int index)> Neg = new List<(bool, int)>();

        /// <summary>置くときに払うマナ</summary>
        public List<string> Pay = new List<string>();

        public static TChoice Place(int hand, int zone, int cell, bool faceUp, List<string> pay = null) =>
            new TChoice { Kind = TChoiceKind.Place, Hand = hand, Zone = zone, Cell = cell, FaceUp = faceUp,
                          Pay = pay ?? new List<string>() };
        public static TChoice Resolve(bool p, int field, int effect, bool apply) =>
            new TChoice { Kind = TChoiceKind.Resolve, Player = p, Field = field, Effect = effect, Apply = apply };
        public static TChoice Attack(int field, int? target, List<(bool, int)> neg) =>
            new TChoice { Kind = TChoiceKind.Attack, Field = field, Target = target, Neg = neg };
        public static TChoice Block(int? target, List<(bool, int)> neg) =>
            new TChoice { Kind = TChoiceKind.Block, Target = target, Neg = neg };
        public static TChoice Tap(int field) => new TChoice { Kind = TChoiceKind.Tap, Field = field };
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
            return new Match { G = g, Turn = new TurnInfo { Tp = first } };
        }

        /// <summary>Match.step?：選んだ動きをしたあとの状態（できない動きなら null）</summary>
        public Match Step(Rules r, TChoice ch)
        {
            var p = Turn.Tp;
            // ブロックを待っている間は、ブロックしかできない
            if (Turn.Pending != null)
            {
                if (ch.Kind != TChoiceKind.Block) return null;
                var opp = G.Get(!p).Field;
                if (!Turn.BlockOK(r, opp, ch.Target)) return null;
                var g = G.Step(r, Choice.Attack(p, Turn.Pending.Value, ch.Target, ch.Neg));
                if (g == null) return null;
                var t = Turn.Copy();
                t.Pending = null;
                if (ch.Target is int j && j >= 0 && j < opp.Count) t.Blocked.Insert(0, opp[j]);
                return new Match { G = g, Turn = t.Pruned(g) };
            }
            switch (ch.Kind)
            {
                case TChoiceKind.Block:
                    return null;
                case TChoiceKind.Place:
                {
                    var hand = G.Get(p).Hand;
                    if (ch.Hand < 0 || ch.Hand >= hand.Count) return null;
                    var sl = new Slot(ch.Zone, ch.Cell, hand[ch.Hand], ch.FaceUp);
                    if (!Turn.PlaceOK(r, sl, ch.Pay)) return null;
                    var g = G.Step(r, Choice.Place(p, ch.Hand, ch.Zone, ch.Cell, ch.FaceUp));
                    if (g == null) return null;
                    var t = Turn.Copy();
                    t.Summons += MatchState.Fights(r, sl) ? 1 : 0;
                    t.Placed.Add(sl.Card.Type);
                    t.Entered.Insert(0, sl);
                    foreach (var x in ch.Pay) t.Pool.Remove(x);
                    return new Match { G = g, Turn = t.Pruned(g) };
                }
                case TChoiceKind.Resolve:
                {
                    var g = G.Step(r, Choice.Resolve(ch.Player, ch.Field, ch.Effect, ch.Apply));
                    if (g == null) return null;
                    return new Match { G = g, Turn = Turn.Pruned(g) };
                }
                case TChoiceKind.Attack:
                {
                    var field = G.Get(p).Field;
                    if (ch.Field < 0 || ch.Field >= field.Count) return null;
                    var sl = field[ch.Field];
                    if (!Turn.AttackOK(r, field, sl)) return null;
                    var t = Turn.Copy();
                    t.Attacked.Insert(0, sl);
                    if (r.AttackTaps) t.Tapped.Insert(0, sl);
                    if (r.Blocking)
                    {
                        // 攻撃の宣言：相手がブロックを選ぶまで待つ
                        if (!(sl.FaceUp && MatchState.Fights(r, sl) && ch.Target == null)) return null;
                        t.Pending = ch.Field;
                        return new Match { G = G, Turn = t.Pruned(G) };
                    }
                    var g = G.Step(r, Choice.Attack(p, ch.Field, ch.Target, ch.Neg));
                    if (g == null) return null;
                    return new Match { G = g, Turn = t.Pruned(g) };
                }
                case TChoiceKind.Tap:
                {
                    var field = G.Get(p).Field;
                    if (ch.Field < 0 || ch.Field >= field.Count) return null;
                    var sl = field[ch.Field];
                    if (!Turn.TapOK(r, field, sl)) return null;
                    var t = Turn.Copy();
                    t.Pool.AddRange(Enumerable.Repeat(sl.Card.ManaColor, sl.Card.Mana));
                    t.Tapped.Insert(0, sl);
                    return new Match { G = G, Turn = t.Pruned(G) };
                }
                default:
                {
                    var g = DrawUpTo(r, !p, r.DrawPerTurn, G);
                    var t = new TurnInfo { Tp = !p, Count = Turn.Count + 1, OppTapped = Turn.Tapped.ToList() };
                    return new Match { G = g, Turn = t.Pruned(g) };
                }
            }
        }

        /// <summary>このターンにこのカードを置けるか（召喚の上限・種類ごとの上限・マナ。置ける場所は MatchState.Step が決める）</summary>
        public bool SummonOK(Rules r, Slot sl, List<string> pay) => Turn.PlaceOK(r, sl, pay);

        /// <summary>このターンに攻撃できる時期か（先攻の最初のターンでないか、ルールで許されているか）</summary>
        public bool AttackPhaseOK(Rules r) => r.FirstTurnAttack || Turn.Count != 1;
    }
}
