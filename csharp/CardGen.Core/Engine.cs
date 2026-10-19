// 盤面の計算（CardGen/Model.lean・Negation.lean・Explore.lean と同じ意味）。
using System.Collections.Generic;
using System.Linq;

namespace CardGen
{
    /// <summary>フィールドのゾーン（デッキ・墓地以外）に置かれたカード</summary>
    public sealed class Slot
    {
        public int Zone;
        /// <summary>ゾーンの何番目のマスか</summary>
        public int Cell;
        public Card Card;
        public bool FaceUp;
        /// <summary>受けているダメージ（ターンの終わりに 0 に戻る）</summary>
        public int Damage;
        /// <summary>ターンの終わりまでの攻撃力・守備力の変化</summary>
        public int AtkBonus, DefBonus;
        /// <summary>同じカードを見分ける鍵（ダメージが変わっても同じ。無効の判定が、適用された順番を覚えるのに使う）</summary>
        public readonly object Key;
        public Slot(int zone, int cell, Card card, bool faceUp, int damage = 0, int atkBonus = 0, int defBonus = 0)
            : this(zone, cell, card, faceUp, damage, atkBonus, defBonus, new object()) { }
        Slot(int zone, int cell, Card card, bool faceUp, int damage, int atkBonus, int defBonus, object key)
        { Zone = zone; Cell = cell; Card = card; FaceUp = faceUp; Damage = damage; AtkBonus = atkBonus; DefBonus = defBonus; Key = key; }

        /// <summary>ダメージとターンの終わりまでの変化だけ変えたもの（同じカード）</summary>
        public Slot With(int damage, int atkBonus, int defBonus) =>
            damage == Damage && atkBonus == AtkBonus && defBonus == DefBonus ? this
                : new Slot(Zone, Cell, Card, FaceUp, damage, atkBonus, defBonus, Key);

        /// <summary>ダメージだけ変えたもの（同じカード）</summary>
        public Slot WithDamage(int damage) => With(damage, AtkBonus, DefBonus);

        /// <summary>Slot.base：ダメージとターンの終わりまでの変化を除いたもの</summary>
        public Slot Base() => With(0, 0, 0);

        /// <summary>ダメージを除いて同じか（ゾーン・マス・カード・表裏）</summary>
        public bool SameBase(Slot b) => Zone == b.Zone && Cell == b.Cell && Card.Name == b.Card.Name && FaceUp == b.FaceUp;

        /// <summary>Slot.view：owner のフィールドのこのカードを、効果を出したもの src から見た情報</summary>
        public View ViewFor(Rules r, bool owner, Src src)
        {
            var c = r.CellOf(owner, Zone, Cell);
            var adj = src.Cell.HasValue && c.HasValue && src.Cell.Value.Adjacent(c.Value);
            var col = src.Cell.HasValue && c.HasValue && src.Cell.Value.Col == c.Value.Col;
            var tgt = src.Target is (bool, Slot) t && t.Item1 == owner && t.Item2.SameBase(this);
            return new View(Card.Type, Card.Tags, owner == src.Player, FaceUp, false, adj, col, tgt);
        }
    }

    /// <summary>Src：効果を出したもの（効果の持ち主と、効果を持つカードのマス）</summary>
    public readonly struct Src
    {
        public readonly bool Player;
        public readonly Cell? Cell;
        /// <summary>解決するときに選んだ対象（プレイヤーとカード）</summary>
        public readonly (bool, Slot)? Target;
        public Src(bool player, Cell? cell, (bool, Slot)? target = null) { Player = player; Cell = cell; Target = target; }
    }

    /// <summary>1人分の状態</summary>
    public sealed class PState
    {
        public List<Card> Deck = new List<Card>();
        public List<Card> Hand = new List<Card>();
        public List<Card> Grave = new List<Card>();
        public List<Slot> Field = new List<Slot>();
        public int Life;

        /// <summary>PState.destroy：owner のフィールド上の、範囲に合うカードをすべて破壊して墓地へ送る</summary>
        public PState Destroy(Rules r, Selector sel, bool owner, Src src)
        {
            bool Hit(Slot sl) => r.OnFieldZone(sl.Zone) && sel.Matches(sl.ViewFor(r, owner, src));
            return new PState
            {
                Deck = Deck.ToList(),
                Hand = Hand.ToList(),
                Field = Field.Where(sl => !Hit(sl)).ToList(),
                Grave = Grave.Concat(Field.Where(Hit).Select(sl => sl.Card)).ToList(),
                Life = Life,
            };
        }
    }

    public static class PStateActions
    {
        /// <summary>PState.bounce：フィールド上の、範囲に合うカードをすべて手札に戻す</summary>
        public static PState Bounce(this PState s, Rules r, Selector sel, bool owner, Src src)
        {
            bool Hit(Slot sl) => r.OnFieldZone(sl.Zone) && sel.Matches(sl.ViewFor(r, owner, src));
            return new PState
            {
                Deck = s.Deck.ToList(),
                Hand = s.Hand.Concat(s.Field.Where(Hit).Select(sl => sl.Card)).ToList(),
                Grave = s.Grave.ToList(),
                Field = s.Field.Where(sl => !Hit(sl)).ToList(),
                Life = s.Life,
            };
        }

        /// <summary>PState.drawN：デッキから n 枚引く（足りなければある分だけ）</summary>
        public static PState DrawN(this PState s, int n) => new PState
        {
            Deck = s.Deck.Skip(n).ToList(),
            Hand = s.Hand.Concat(s.Deck.Take(n)).ToList(),
            Grave = s.Grave.ToList(),
            Field = s.Field.ToList(),
            Life = s.Life,
        };

        /// <summary>PState.damage：ダメージを受ける（ライフは 0 より下がらない）</summary>
        public static PState Damage(this PState s, int n) => s.With(life: System.Math.Max(0, s.Life - n));

        /// <summary>PState.destroyAt：フィールドの k 番目のカードを破壊して墓地へ送る</summary>
        public static PState DestroyAt(this PState s, int k)
        {
            if (k < 0 || k >= s.Field.Count) return s;
            var n = s.With();
            n.Grave.Add(s.Field[k].Card);
            n.Field.RemoveAt(k);
            return n;
        }

        /// <summary>PState.mark：フィールドの i 番目のカードにダメージ d(i) を加える</summary>
        public static PState Mark(this PState s, System.Func<int, int> d)
        {
            var n = s.With();
            n.Field = s.Field.Select((sl, i) => sl.WithDamage(sl.Damage + d(i))).ToList();
            return n;
        }

        /// <summary>PState.counter：範囲に合う「フィールド上」でないゾーンのカードを、すべて墓地へ送る（打ち消す）</summary>
        public static PState Counter(this PState s, Rules r, Selector sel, bool owner, Src src)
        {
            bool Hit(Slot sl) => !r.OnFieldZone(sl.Zone) && sel.Matches(sl.ViewFor(r, owner, src));
            var n = s.With();
            n.Field = s.Field.Where(sl => !Hit(sl)).ToList();
            n.Grave.AddRange(s.Field.Where(Hit).Select(sl => sl.Card));
            return n;
        }

        /// <summary>PState.pump：フィールドの i 番目のカードの攻撃力・守備力を、ターンの終わりまで d(i) だけ変える</summary>
        public static PState Pump(this PState s, System.Func<int, (int, int)> d)
        {
            var n = s.With();
            n.Field = s.Field.Select((sl, i) => sl.With(sl.Damage, sl.AtkBonus + d(i).Item1, sl.DefBonus + d(i).Item2)).ToList();
            return n;
        }

        /// <summary>PState.sweep：フィールドの i 番目のカード sl のうち、dead(i, sl) のものを破壊して墓地へ送る</summary>
        public static PState Sweep(this PState s, System.Func<int, Slot, bool> dead)
        {
            var n = s.With();
            n.Field = s.Field.Where((sl, i) => !dead(i, sl)).ToList();
            n.Grave.AddRange(s.Field.Where((sl, i) => dead(i, sl)).Select(sl => sl.Card));
            return n;
        }

        /// <summary>写し（ライフだけ変えることもできる）</summary>
        public static PState With(this PState s, int? life = null) => new PState
        {
            Deck = s.Deck.ToList(), Hand = s.Hand.ToList(), Grave = s.Grave.ToList(), Field = s.Field.ToList(),
            Life = life ?? s.Life,
        };
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

        /// <summary>安定な状態をすべて返す（各カードが有効なら true）。カードが多すぎるときは null</summary>
        public static List<bool[]> StableStates(IReadOnlyList<Inst> insts, int maxCards = 16)
        {
            int n = insts.Count;
            if (n > maxCards) return null;
            var rel = new bool[n, n];
            for (int y = 0; y < n; y++)
                for (int x = 0; x < n; x++)
                    rel[y, x] = InstRel(insts, y, x);
            var result = new List<bool[]>();
            for (int s = 0; s < (1 << n); s++)
            {
                bool stable = true;
                for (int x = 0; x < n && stable; x++)
                {
                    bool negated = false;
                    for (int y = 0; y < n; y++) if (rel[y, x] && ((s >> y) & 1) == 1) { negated = true; break; }
                    if ((((s >> x) & 1) == 1) == negated) stable = false;
                }
                if (stable) result.Add(Enumerable.Range(0, n).Select(x => ((s >> x) & 1) == 1).ToArray());
            }
            return result;
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
