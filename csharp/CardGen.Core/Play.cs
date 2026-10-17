// 対戦の進行（CardGen/Model.lean の start と、CardGen/Play.lean の State.step? と同じ意味）。
using System.Collections.Generic;
using System.Linq;

namespace CardGen
{
    public enum ChoiceKind { Draw, Place, Resolve }

    /// <summary>プレイヤーが選ぶ動き（Choice）</summary>
    public sealed class Choice
    {
        public ChoiceKind Kind;
        /// <summary>動くプレイヤー（true と false の2人）</summary>
        public bool Player;
        public int Hand, Zone, Field, Effect;
        public bool FaceUp, Apply;

        public static Choice Draw(bool p) => new Choice { Kind = ChoiceKind.Draw, Player = p };
        public static Choice Place(bool p, int hand, int zone, bool faceUp) =>
            new Choice { Kind = ChoiceKind.Place, Player = p, Hand = hand, Zone = zone, FaceUp = faceUp };
        public static Choice Resolve(bool p, int field, int effect, bool apply) =>
            new Choice { Kind = ChoiceKind.Resolve, Player = p, Field = field, Effect = effect, Apply = apply };
    }

    /// <summary>対戦の状態（2人分）</summary>
    public sealed class MatchState
    {
        public PState P1 = new PState();
        public PState P2 = new PState();

        public PState Get(bool p) => p ? P1 : P2;
        public MatchState With(bool p, PState s) => p ? new MatchState { P1 = s, P2 = P2 } : new MatchState { P1 = P1, P2 = s };

        static PState Copy(PState s) => new PState
        {
            Deck = s.Deck.ToList(), Hand = s.Hand.ToList(), Grave = s.Grave.ToList(), Field = s.Field.ToList(),
        };

        /// <summary>start：それぞれのデッキから初期手札を引いた状態</summary>
        public static MatchState Start(Rules r, List<Card> deck1, List<Card> deck2)
        {
            PState Of(List<Card> d) => new PState { Deck = d.Skip(r.HandSize).ToList(), Hand = d.Take(r.HandSize).ToList() };
            return new MatchState { P1 = Of(deck1), P2 = Of(deck2) };
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
                    var room = z.Capacity != Capacity.One || s.Field.Count(sl => sl.Zone == ch.Zone) < z.Count;
                    if (z.Role != ZoneRole.Plain || !z.Admits.Contains(c.Type) || !room) return null;
                    var n = Copy(s);
                    // List.erase：同じカードのうち最初の1枚を取り除く
                    n.Hand.RemoveAt(n.Hand.FindIndex(x => x.Name == c.Name));
                    n.Field.Add(new Slot(ch.Zone, c, ch.FaceUp));
                    return With(p, n);
                }
                default:
                {
                    if (ch.Field < 0 || ch.Field >= s.Field.Count) return null;
                    var sl = s.Field[ch.Field];
                    if (ch.Effect < 0 || ch.Effect >= sl.Card.Effects.Count || !(sl.Card.Effects[ch.Effect] is Activated act)) return null;
                    var n1 = Copy(s);
                    n1.Field.RemoveAt(ch.Field);
                    var g = With(p, n1);
                    if (ch.Apply)
                        foreach (var a in act.Actions)
                            if (a is Destroy d)
                                g = new MatchState
                                {
                                    P1 = g.P1.Destroy(r, d.Target, p == true),
                                    P2 = g.P2.Destroy(r, d.Target, p == false),
                                };
                    var last = Copy(g.Get(p));
                    last.Grave.Add(sl.Card);
                    return g.With(p, last);
                }
            }
        }
    }
}
