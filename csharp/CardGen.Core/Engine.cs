// 盤面の計算（CardGen/Model.lean・Negation.lean・Explore.lean と同じ意味）。
using System.Collections.Generic;
using System.Linq;

namespace CardGen
{
    /// <summary>フィールドのゾーン（デッキ・墓地以外）に置かれたカード</summary>
    public sealed class Slot
    {
        public int Zone;
        public Card Card;
        public bool FaceUp;
        public Slot(int zone, Card card, bool faceUp) { Zone = zone; Card = card; FaceUp = faceUp; }

        public View ViewFor(bool mine) => new View(Card.Type, Card.Tags, mine, FaceUp, false);
    }

    /// <summary>1人分の状態</summary>
    public sealed class PState
    {
        public List<Card> Deck = new List<Card>();
        public List<Card> Hand = new List<Card>();
        public List<Card> Grave = new List<Card>();
        public List<Slot> Field = new List<Slot>();

        /// <summary>PState.destroy：フィールド上の、範囲に合うカードをすべて破壊して墓地へ送る</summary>
        public PState Destroy(Rules r, Selector sel, bool mine)
        {
            bool Hit(Slot sl) => r.OnFieldZone(sl.Zone) && sel.Matches(sl.ViewFor(mine));
            return new PState
            {
                Deck = Deck.ToList(),
                Hand = Hand.ToList(),
                Field = Field.Where(sl => !Hit(sl)).ToList(),
                Grave = Grave.Concat(Field.Where(Hit).Select(sl => sl.Card)).ToList(),
            };
        }
    }

    /// <summary>フィールドに置かれたカード1枚（無効の関係を調べる単位）</summary>
    public sealed class Inst
    {
        public Card Card;
        public bool Controller;
        public bool FaceUp;
        public Inst(Card card, bool controller, bool faceUp) { Card = card; Controller = controller; FaceUp = faceUp; }
    }

    /// <summary>判定の手続きの分類（Verdict）</summary>
    public enum Verdict { Ok, SomeLoop, MultiStable, CannotHalt, NoStable }

    public static class Negation
    {
        /// <summary>instRel：y 番目のカードが x 番目のカードの効果を無効にする</summary>
        public static bool InstRel(IReadOnlyList<Inst> insts, int y, int x)
        {
            if (y < 0 || y >= insts.Count || x < 0 || x >= insts.Count) return false;
            var a = insts[y];
            var b = insts[x];
            if (!a.FaceUp) return false;
            var v = new View(b.Card.Type, b.Card.Tags, b.Controller == a.Controller, b.FaceUp, y == x);
            return a.Card.Effects.OfType<Negate>().Any(n => n.Target.Matches(v));
        }

        /// <summary>analyzeBoard：盤面の判定の手続きを、すべての状態（2^n 通り）について調べる</summary>
        public static Verdict AnalyzeBoard(IReadOnlyList<Inst> insts)
        {
            int n = insts.Count;
            int states = 1 << n;
            var rel = new bool[n, n];
            for (int y = 0; y < n; y++)
                for (int x = 0; x < n; x++)
                    rel[y, x] = InstRel(insts, y, x);

            bool Bit(int s, int x) => ((s >> x) & 1) == 1;
            bool Negated(int s, int x)
            {
                for (int y = 0; y < n; y++) if (rel[y, x] && Bit(s, y)) return true;
                return false;
            }

            var succs = new List<int>[states];
            for (int s = 0; s < states; s++)
            {
                succs[s] = new List<int>();
                for (int x = 0; x < n; x++)
                    if (Bit(s, x) == Negated(s, x)) succs[s].Add(s ^ (1 << x));
            }
            var halting = succs.Select(l => l.Count == 0).ToArray();
            int stables = halting.Count(h => h);
            if (stables == 0) return Verdict.NoStable;

            var canHalt = (bool[])halting.Clone();
            for (var changed = true; changed;)
            {
                changed = false;
                for (int s = 0; s < states; s++)
                    if (!canHalt[s] && succs[s].Any(t => canHalt[t])) { canHalt[s] = true; changed = true; }
            }
            if (canHalt.Any(b => !b)) return Verdict.CannotHalt;
            if (stables > 1) return Verdict.MultiStable;

            var allHalt = (bool[])halting.Clone();
            for (var changed = true; changed;)
            {
                changed = false;
                for (int s = 0; s < states; s++)
                    if (!allHalt[s] && succs[s].All(t => allHalt[t])) { allHalt[s] = true; changed = true; }
            }
            if (allHalt.Any(b => !b)) return Verdict.SomeLoop;
            return Verdict.Ok;
        }
    }
}
