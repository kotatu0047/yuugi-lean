// ビジュアルエディタのノードのグラフと、中間表現との変換。
// ノードの種類とつなぎ方：
//   ルール ──▶ ゾーン（上から順に Rules.zones の順番）
//   カード ──▶ 効果（「発動して破壊」または「無効」）──▶ 範囲
//   「発動して破壊」につないだ範囲1つが、破壊の動き1つになる（上から順に行う）
//   「無効」には範囲をちょうど1つつなぐ
using System.Collections.Generic;
using System.Linq;

namespace CardGen
{
    public enum NodeKind { Rules, Zone, Card, Destroy, Negate, Selector }

    /// <summary>ルールのノードの中身（ゾーンはつないだノードから作る）</summary>
    public sealed class RulesData
    {
        public List<string> CardTypes = new List<string>();
        public int DeckSize;
        public int HandSize;
    }

    /// <summary>カードのノードの中身（効果はつないだノードから作る）</summary>
    public sealed class CardData
    {
        public string Name = "";
        public string Type = "";
        public List<string> Tags = new List<string>();
    }

    public sealed class Node
    {
        public int Id;
        public NodeKind Kind;
        public float X, Y;
        public RulesData Rules;
        public Zone Zone;
        public CardData Card;
        public Selector Selector;

        public static Node Make(int id, NodeKind kind, float x, float y)
        {
            var n = new Node { Id = id, Kind = kind, X = x, Y = y };
            switch (kind)
            {
                case NodeKind.Rules: n.Rules = new RulesData(); break;
                case NodeKind.Zone: n.Zone = new Zone { Count = 1, Role = ZoneRole.Plain, Capacity = Capacity.One }; break;
                case NodeKind.Card: n.Card = new CardData(); break;
                case NodeKind.Selector: n.Selector = new Selector { Side = Side.Both }; break;
            }
            return n;
        }

        public static string KindLabel(NodeKind k) => k switch
        {
            NodeKind.Rules => "ルール",
            NodeKind.Zone => "ゾーン",
            NodeKind.Card => "カード",
            NodeKind.Destroy => "発動して破壊",
            NodeKind.Negate => "無効（永続）",
            _ => "範囲",
        };

        /// <summary>ノードの見出しに出す名前</summary>
        public string Title => Kind switch
        {
            NodeKind.Zone => Zone.Name,
            NodeKind.Card => Card.Name,
            _ => KindLabel(Kind),
        };
    }

    public readonly struct Edge
    {
        public readonly int From;
        public readonly int To;
        public Edge(int from, int to) { From = from; To = to; }
    }

    public sealed class GraphDoc
    {
        public List<Node> Nodes = new List<Node>();
        public List<Edge> Edges = new List<Edge>();

        public int NextId => Nodes.Count == 0 ? 1 : Nodes.Max(n => n.Id) + 1;

        public Node Find(int id) => Nodes.FirstOrDefault(n => n.Id == id);

        /// <summary>つないだ先のノード（上から順）</summary>
        public List<Node> Children(Node n) =>
            Edges.Where(e => e.From == n.Id).Select(e => Find(e.To)).Where(c => c != null).OrderBy(c => c.Y).ThenBy(c => c.X).ToList();

        public List<Node> Parents(Node n) =>
            Edges.Where(e => e.To == n.Id).Select(e => Find(e.From)).Where(c => c != null).ToList();

        /// <summary>from から to へつないでよいか（つなげる種類の組と、入る側の数の制限）</summary>
        public static bool CanConnect(NodeKind from, NodeKind to) =>
            (from == NodeKind.Rules && to == NodeKind.Zone) ||
            (from == NodeKind.Card && (to == NodeKind.Destroy || to == NodeKind.Negate)) ||
            ((from == NodeKind.Destroy || from == NodeKind.Negate) && to == NodeKind.Selector);

        /// <summary>つなぐ。入る側はつなぎ元を1つしか持てないので、前のつなぎは外す</summary>
        public bool Connect(int from, int to)
        {
            var a = Find(from);
            var b = Find(to);
            if (a == null || b == null || !CanConnect(a.Kind, b.Kind)) return false;
            Edges.RemoveAll(e => e.To == to);
            if (a.Kind == NodeKind.Negate) Edges.RemoveAll(e => e.From == from);
            Edges.Add(new Edge(from, to));
            return true;
        }

        public void Remove(int id)
        {
            Nodes.RemoveAll(n => n.Id == id);
            Edges.RemoveAll(e => e.From == id || e.To == id);
        }

        /// <summary>
        /// グラフから中間表現を作る。つなぎ方の問題（ルールがない、範囲がつながっていない など）は
        /// structure に入れ、作れる範囲で中間表現を作る。
        /// </summary>
        public Game ToGame(out List<string> structure)
        {
            structure = new List<string>();
            var rulesNodes = Nodes.Where(n => n.Kind == NodeKind.Rules).ToList();
            var rules = new Rules();
            if (rulesNodes.Count == 0) structure.Add("ルールのノードがありません");
            if (rulesNodes.Count > 1) structure.Add("ルールのノードは1つだけにしてください");
            if (rulesNodes.Count > 0)
            {
                var r = rulesNodes[0];
                rules.CardTypes = r.Rules.CardTypes.ToList();
                rules.DeckSize = r.Rules.DeckSize;
                rules.HandSize = r.Rules.HandSize;
                rules.Zones = Children(r).Select(z => z.Zone).ToList();
            }
            foreach (var z in Nodes.Where(n => n.Kind == NodeKind.Zone && Parents(n).Count == 0))
                structure.Add($"ゾーン「{z.Zone.Name}」がルールにつながっていません");

            var cards = new List<Card>();
            foreach (var c in Nodes.Where(n => n.Kind == NodeKind.Card).OrderBy(n => n.Y).ThenBy(n => n.X))
            {
                var card = new Card { Name = c.Card.Name, Type = c.Card.Type, Tags = c.Card.Tags.ToList() };
                foreach (var e in Children(c))
                {
                    var sels = Children(e).Select(s => s.Selector).ToList();
                    if (e.Kind == NodeKind.Destroy)
                        card.Effects.Add(new Activated(sels.Select(s => (Action)new Destroy(s)).ToList()));
                    else if (sels.Count == 1)
                        card.Effects.Add(new Negate(sels[0]));
                    else
                        structure.Add($"カード「{c.Card.Name}」の無効の効果に、範囲がつながっていません");
                }
                cards.Add(card);
            }
            foreach (var e in Nodes.Where(n => (n.Kind == NodeKind.Destroy || n.Kind == NodeKind.Negate) && Parents(n).Count == 0))
                structure.Add($"{Node.KindLabel(e.Kind)}のノードがカードにつながっていません");
            foreach (var s in Nodes.Where(n => n.Kind == NodeKind.Selector && Parents(n).Count == 0))
                structure.Add("範囲のノードが効果につながっていません");

            return new Game { Rules = rules, Cards = cards };
        }

        /// <summary>中間表現からグラフを作り、ノードを並べる</summary>
        public static GraphDoc FromGame(Game g)
        {
            var doc = new GraphDoc();
            int id = 1;
            Node Add(NodeKind k, float x, float y)
            {
                var n = Node.Make(id++, k, x, y);
                doc.Nodes.Add(n);
                return n;
            }

            var r = Add(NodeKind.Rules, 40, 40);
            r.Rules.CardTypes = g.Rules.CardTypes.ToList();
            r.Rules.DeckSize = g.Rules.DeckSize;
            r.Rules.HandSize = g.Rules.HandSize;
            float zy = 40;
            foreach (var z in g.Rules.Zones)
            {
                var zn = Add(NodeKind.Zone, 320, zy);
                zn.Zone = z;
                doc.Edges.Add(new Edge(r.Id, zn.Id));
                zy += 110;
            }

            float cy = Mathf.Max(zy + 40, 520);
            foreach (var c in g.Cards)
            {
                var cn = Add(NodeKind.Card, 40, cy);
                cn.Card = new CardData { Name = c.Name, Type = c.Type, Tags = c.Tags.ToList() };
                float ey = cy;
                foreach (var e in c.Effects)
                {
                    var sels = e switch
                    {
                        Activated a => a.Actions.OfType<Destroy>().Select(d => d.Target).ToList(),
                        Negate n => new List<Selector> { n.Target },
                        _ => new List<Selector>(),
                    };
                    var en = Add(e is Activated ? NodeKind.Destroy : NodeKind.Negate, 320, ey);
                    doc.Edges.Add(new Edge(cn.Id, en.Id));
                    float sy = ey;
                    foreach (var s in sels)
                    {
                        var sn = Add(NodeKind.Selector, 580, sy);
                        sn.Selector = s;
                        doc.Edges.Add(new Edge(en.Id, sn.Id));
                        sy += 130;
                    }
                    ey = Mathf.Max(ey + 90, sy);
                }
                cy = Mathf.Max(cy + 110, ey + 20);
            }
            return doc;
        }

        static class Mathf
        {
            public static float Max(float a, float b) => a > b ? a : b;
        }
    }
}
