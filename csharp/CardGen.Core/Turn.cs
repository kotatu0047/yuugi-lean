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

        /// <summary>Lean の Slot の等しさ（ゾーン・カード・表裏が同じ）</summary>
        public static bool SameSlot(Slot a, Slot b) => a.Zone == b.Zone && a.Card.Name == b.Card.Name && a.FaceUp == b.FaceUp;

        static int CountOf(IEnumerable<Slot> l, Slot s) => l.Count(x => SameSlot(x, s));

        /// <summary>prune：攻撃したカードの記録を、今のフィールドにあるものだけに絞る（同じカードはある枚数まで）</summary>
        public static List<Slot> Prune(List<Slot> attacked, List<Slot> field)
        {
            var rest = field.ToList();
            var result = new List<Slot>();
            foreach (var a in attacked)
            {
                int i = rest.FindIndex(x => SameSlot(x, a));
                if (i < 0) continue;
                result.Add(a);
                rest.RemoveAt(i);
            }
            return result;
        }

        /// <summary>このカードはこのターンにまだ攻撃できるか（同じカードの、攻撃した枚数がフィールドの枚数より少ない）</summary>
        public bool CanAttack(Slot sl, List<Slot> field) => CountOf(Attacked, sl) < CountOf(field, sl);

        public TurnInfo With(int? summons = null, List<Slot> attacked = null) => new TurnInfo
        {
            Tp = Tp, Count = Count, Summons = summons ?? Summons, Attacked = attacked ?? Attacked.ToList(),
        };
    }

    public enum TChoiceKind { Place, Resolve, Attack, EndTurn }

    /// <summary>ターンのある対戦の動き（TChoice）</summary>
    public sealed class TChoice
    {
        public TChoiceKind Kind;
        /// <summary>発動するプレイヤー（Resolve のみ。ほかはターンプレイヤー）</summary>
        public bool Player;
        public int Hand, Zone, Field, Effect;
        public bool FaceUp, Apply;
        public int? Target;
        public List<(bool player, int index)> Neg = new List<(bool, int)>();

        public static TChoice Place(int hand, int zone, bool faceUp) =>
            new TChoice { Kind = TChoiceKind.Place, Hand = hand, Zone = zone, FaceUp = faceUp };
        public static TChoice Resolve(bool p, int field, int effect, bool apply) =>
            new TChoice { Kind = TChoiceKind.Resolve, Player = p, Field = field, Effect = effect, Apply = apply };
        public static TChoice Attack(int field, int? target, List<(bool, int)> neg) =>
            new TChoice { Kind = TChoiceKind.Attack, Field = field, Target = target, Neg = neg };
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

        TurnInfo Pruned(TurnInfo t, MatchState g) => t.With(attacked: TurnInfo.Prune(t.Attacked, g.Get(t.Tp).Field));

        /// <summary>Match.step?：選んだ動きをしたあとの状態（できない動きなら null）</summary>
        public Match Step(Rules r, TChoice ch)
        {
            var p = Turn.Tp;
            switch (ch.Kind)
            {
                case TChoiceKind.Place:
                {
                    var hand = G.Get(p).Hand;
                    if (ch.Hand < 0 || ch.Hand >= hand.Count) return null;
                    var fighter = MatchState.Fights(r, new Slot(ch.Zone, hand[ch.Hand], ch.FaceUp));
                    if (fighter && r.SummonsPerTurn != 0 && Turn.Summons >= r.SummonsPerTurn) return null;
                    var g = G.Step(r, Choice.Place(p, ch.Hand, ch.Zone, ch.FaceUp));
                    if (g == null) return null;
                    return new Match { G = g, Turn = Turn.With(summons: Turn.Summons + (fighter ? 1 : 0)) };
                }
                case TChoiceKind.Resolve:
                {
                    var g = G.Step(r, Choice.Resolve(ch.Player, ch.Field, ch.Effect, ch.Apply));
                    if (g == null) return null;
                    return new Match { G = g, Turn = Pruned(Turn, g) };
                }
                case TChoiceKind.Attack:
                {
                    var field = G.Get(p).Field;
                    if (ch.Field < 0 || ch.Field >= field.Count) return null;
                    var sl = field[ch.Field];
                    if (!(r.FirstTurnAttack || Turn.Count != 1)) return null;
                    if (!Turn.CanAttack(sl, field)) return null;
                    var g = G.Step(r, Choice.Attack(p, ch.Field, ch.Target, ch.Neg));
                    if (g == null) return null;
                    var attacked = new List<Slot> { sl };
                    attacked.AddRange(Turn.Attacked);
                    return new Match { G = g, Turn = Pruned(Turn.With(attacked: attacked), g) };
                }
                default:
                {
                    var q = !p;
                    return new Match { G = DrawUpTo(r, q, r.DrawPerTurn, G), Turn = new TurnInfo { Tp = q, Count = Turn.Count + 1 } };
                }
            }
        }

        /// <summary>このターンにこのカードを置けるか（召喚の上限だけを見る。置ける場所は MatchState.Step が決める）</summary>
        public bool SummonOK(Rules r, Slot sl) =>
            !MatchState.Fights(r, sl) || r.SummonsPerTurn == 0 || Turn.Summons < r.SummonsPerTurn;

        /// <summary>このターンに攻撃できる時期か（先攻の最初のターンでないか、ルールで許されているか）</summary>
        public bool AttackPhaseOK(Rules r) => r.FirstTurnAttack || Turn.Count != 1;
    }
}
