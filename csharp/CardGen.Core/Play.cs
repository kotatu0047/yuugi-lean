// 対戦の進行（CardGen/Model.lean の start と、CardGen/Play.lean の State.step? と同じ意味）。
using System.Collections.Generic;
using System.Linq;

namespace CardGen
{
    public enum ChoiceKind { Draw, Place, Resolve, Attack }

    /// <summary>プレイヤーが選ぶ動き（Choice）</summary>
    public sealed class Choice
    {
        public ChoiceKind Kind;
        /// <summary>動くプレイヤー（true と false の2人）</summary>
        public bool Player;
        public int Hand, Zone, Cell, Field, Effect;
        public bool FaceUp, Apply;
        /// <summary>攻撃の対象（相手のフィールドの何番目か。null なら直接攻撃）</summary>
        public int? Target;
        /// <summary>効果が無効になっているカードの位置（攻撃力の計算に使う）</summary>
        public List<(bool player, int index)> Neg = new List<(bool, int)>();

        public static Choice Draw(bool p) => new Choice { Kind = ChoiceKind.Draw, Player = p };
        public static Choice Place(bool p, int hand, int zone, int cell, bool faceUp) =>
            new Choice { Kind = ChoiceKind.Place, Player = p, Hand = hand, Zone = zone, Cell = cell, FaceUp = faceUp };
        public static Choice Resolve(bool p, int field, int effect, bool apply) =>
            new Choice { Kind = ChoiceKind.Resolve, Player = p, Field = field, Effect = effect, Apply = apply };
        public static Choice Attack(bool p, int field, int? target, List<(bool, int)> neg) =>
            new Choice { Kind = ChoiceKind.Attack, Player = p, Field = field, Target = target, Neg = neg };
    }

    /// <summary>対戦の状態（2人分）</summary>
    public sealed class MatchState
    {
        public PState P1 = new PState();
        public PState P2 = new PState();

        public PState Get(bool p) => p ? P1 : P2;
        public MatchState With(bool p, PState s) => p ? new MatchState { P1 = s, P2 = P2 } : new MatchState { P1 = P1, P2 = s };

        static PState Copy(PState s) => s.With();

        /// <summary>start：それぞれのデッキから初期手札を引いた状態</summary>
        public static MatchState Start(Rules r, List<Card> deck1, List<Card> deck2)
        {
            PState Of(List<Card> d) => new PState { Deck = d.Skip(r.HandSize).ToList(), Hand = d.Take(r.HandSize).ToList(), Life = r.Life };
            return new MatchState { P1 = Of(deck1), P2 = Of(deck2) };
        }

        /// <summary>フィールド上（「フィールド上」に数えるゾーン）のカード。無効の関係を調べる単位</summary>
        public List<(bool player, int index, Inst inst)> FieldInsts(Rules r)
        {
            var l = new List<(bool, int, Inst)>();
            foreach (var p in new[] { true, false })
            {
                var f = Get(p).Field;
                for (int i = 0; i < f.Count; i++)
                    if (r.OnFieldZone(f[i].Zone)) l.Add((p, i, new Inst(f[i].Card, p, f[i].FaceUp)));
            }
            return l;
        }

        /// <summary>盤面の制約（Lean の Inv）が成り立っているか。成り立たない項目を返す</summary>
        public List<string> Violations(Rules r)
        {
            var v = new List<string>();
            foreach (var p in new[] { true, false })
            {
                var s = Get(p);
                var who = p ? "自分" : "相手";
                var size = s.Deck.Count + s.Hand.Count + s.Grave.Count + s.Field.Count;
                if (size != r.DeckSize) v.Add($"{who}のカードの枚数が {size} 枚（デッキの枚数は {r.DeckSize} 枚）");
                foreach (var sl in s.Field)
                {
                    var ok = sl.Zone >= 0 && sl.Zone < r.Zones.Count && r.Zones[sl.Zone].Role == ZoneRole.Plain &&
                             r.Zones[sl.Zone].Admits.Contains(sl.Card.Type);
                    if (!ok) v.Add($"{who}の「{sl.Card.Name}」は置けないゾーンにあります");
                }
                foreach (var sl in s.Field)
                    if (sl.Zone >= 0 && sl.Zone < r.Zones.Count && (sl.Cell < 0 || sl.Cell >= r.Zones[sl.Zone].Count))
                        v.Add($"{who}の「{sl.Card.Name}」は「{r.Zones[sl.Zone].Name}」にない {sl.Cell} 番目のマスにあります");
                for (int i = 0; i < s.Field.Count; i++)
                    for (int j = i + 1; j < s.Field.Count; j++)
                    {
                        var a = s.Field[i];
                        var b = s.Field[j];
                        if (a.Zone == b.Zone && a.Cell == b.Cell && a.Zone >= 0 && a.Zone < r.Zones.Count &&
                            r.Zones[a.Zone].Capacity == Capacity.One)
                            v.Add($"{who}の「{r.Zones[a.Zone].Name}」の {a.Cell} 番目のマスに2枚（「{a.Card.Name}」と「{b.Card.Name}」）");
                    }
            }
            return v;
        }

        /// <summary>Rules.fights：戦闘できる「フィールド上」のカードか</summary>
        public static bool Fights(Rules r, Slot sl) => r.OnFieldZone(sl.Zone) && r.Fighters.Contains(sl.Card.Type);

        /// <summary>State.targetOK：攻撃の対象として選べるか（null は直接攻撃：相手に戦闘できるカードがないとき）</summary>
        public bool TargetOK(Rules r, bool p, int? target)
        {
            var o = Get(!p).Field;
            if (target == null) return o.All(t => !Fights(r, t));
            var j = target.Value;
            return j >= 0 && j < o.Count && Fights(r, o[j]);
        }

        /// <summary>boostFrom：q のフィールドの j 番目のカード src の効果で、位置 t のカード tsl の攻撃力が変わる量</summary>
        static long BoostFrom(Rules r, List<(bool, int)> neg, (bool p, int i) t, Slot tsl, bool q, int j, Slot src)
        {
            if (!src.FaceUp || !r.OnFieldZone(src.Zone) || neg.Contains((q, j))) return 0;
            var w = tsl.ViewFor(r, t.p, new Src(q, r.CellOf(q, src.Zone, src.Cell)));
            var v = new View(w.Type, w.Tags, w.Mine, w.FaceUp, q == t.p && j == t.i, w.Adjacent, w.SameColumn);
            return src.Card.Effects.OfType<Boost>().Where(b => b.Target.Matches(v)).Sum(b => (long)b.Amount);
        }

        /// <summary>State.atkOf：位置 t のカード tsl の攻撃力（元の攻撃力に、無効でない「攻撃力を変える」効果を足す。0 未満は 0）</summary>
        public int AtkOf(Rules r, List<(bool, int)> neg, (bool p, int i) t, Slot tsl)
        {
            long sum = tsl.Card.Attack;
            foreach (var q in new[] { true, false })
            {
                var f = Get(q).Field;
                for (int j = 0; j < f.Count; j++) sum += BoostFrom(r, neg, t, tsl, q, j, f[j]);
            }
            return (int)System.Math.Max(0, sum);
        }

        /// <summary>State.battle：p のフィールドの k 番目のカード sl で、相手の target 番目のカード（null なら直接）を攻撃したあとの状態</summary>
        public MatchState Battle(Rules r, List<(bool, int)> neg, bool p, int k, Slot sl, int? target)
        {
            var o = !p;
            var a = AtkOf(r, neg, (p, k), sl);
            if (target == null) return With(o, Get(o).Damage(a));
            var j = target.Value;
            if (j < 0 || j >= Get(o).Field.Count) return this;
            var tl = Get(o).Field[j];
            if (tl.FaceUp)
            {
                var t = AtkOf(r, neg, (o, j), tl);
                if (t < a) return With(o, Get(o).DestroyAt(j).Damage(a - t));
                if (a < t) return With(p, Get(p).DestroyAt(k).Damage(t - a));
                if (a == 0) return this;
                return With(p, Get(p).DestroyAt(k)).With(o, Get(o).DestroyAt(j));
            }
            var d = tl.Card.Defense;
            if (d < a) return With(o, Get(o).DestroyAt(j));
            if (a < d) return With(p, Get(p).Damage(d - a));
            return this;
        }

        /// <summary>State.freeCell：p の i 番目のゾーンの、空いている最初のマス（なければ 0。「何枚でも」のゾーンなら 0）</summary>
        public int FreeCell(Rules r, bool p, int i)
        {
            if (i < 0 || i >= r.Zones.Count) return 0;
            var z = r.Zones[i];
            if (z.Capacity != Capacity.One) return 0;
            for (int j = 0; j < z.Count; j++)
                if (Get(p).Field.All(sl => !(sl.Zone == i && sl.Cell == j))) return j;
            return 0;
        }

        /// <summary>State.step?：選んだ動きをしたあとの状態（できない動きなら null）</summary>
        public MatchState Step(Rules r, Choice ch)
        {
            var p = ch.Player;
            var s = Get(p);
            switch (ch.Kind)
            {
                case ChoiceKind.Draw:
                {
                    if (s.Deck.Count == 0) return null;
                    var n = Copy(s);
                    var c = n.Deck[0];
                    n.Deck.RemoveAt(0);
                    n.Hand.Add(c);
                    return With(p, n);
                }
                case ChoiceKind.Place:
                {
                    if (ch.Hand < 0 || ch.Hand >= s.Hand.Count || ch.Zone < 0 || ch.Zone >= r.Zones.Count) return null;
                    var c = s.Hand[ch.Hand];
                    var z = r.Zones[ch.Zone];
                    var free = z.Capacity != Capacity.One || s.Field.All(sl => !(sl.Zone == ch.Zone && sl.Cell == ch.Cell));
                    if (z.Role != ZoneRole.Plain || !z.Admits.Contains(c.Type) || ch.Cell < 0 || ch.Cell >= z.Count || !free)
                        return null;
                    var n = Copy(s);
                    // List.erase：同じカードのうち最初の1枚を取り除く
                    n.Hand.RemoveAt(n.Hand.FindIndex(x => x.Name == c.Name));
                    n.Field.Add(new Slot(ch.Zone, ch.Cell, c, ch.FaceUp));
                    return With(p, n);
                }
                case ChoiceKind.Attack:
                {
                    if (ch.Field < 0 || ch.Field >= s.Field.Count) return null;
                    var sl = s.Field[ch.Field];
                    if (!sl.FaceUp || !Fights(r, sl) || !TargetOK(r, p, ch.Target)) return null;
                    return Battle(r, ch.Neg, p, ch.Field, sl, ch.Target);
                }
                default:
                {
                    if (ch.Field < 0 || ch.Field >= s.Field.Count) return null;
                    var sl = s.Field[ch.Field];
                    if (ch.Effect < 0 || ch.Effect >= sl.Card.Effects.Count || !(sl.Card.Effects[ch.Effect] is Activated act)) return null;
                    var n1 = Copy(s);
                    n1.Field.RemoveAt(ch.Field);
                    var g = With(p, n1);
                    var src = new Src(p, r.CellOf(p, sl.Zone, sl.Cell));
                    if (ch.Apply)
                        foreach (var a in act.Actions)
                            g = a switch
                            {
                                Destroy d => new MatchState { P1 = g.P1.Destroy(r, d.Target, true, src), P2 = g.P2.Destroy(r, d.Target, false, src) },
                                Bounce b => new MatchState { P1 = g.P1.Bounce(r, b.Target, true, src), P2 = g.P2.Bounce(r, b.Target, false, src) },
                                DrawCards dc => g.With(p, g.Get(p).DrawN(dc.Count)),
                                Damage dm => g.With(!p, g.Get(!p).Damage(dm.Amount)),
                                Heal h => g.With(p, g.Get(p).With(life: g.Get(p).Life + h.Amount)),
                                _ => g,
                            };
                    var last = Copy(g.Get(p));
                    last.Grave.Add(sl.Card);
                    return g.With(p, last);
                }
            }
        }
    }
}
