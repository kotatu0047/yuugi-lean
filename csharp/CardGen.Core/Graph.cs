// ビジュアルエディタのノードのグラフと、中間表現との変換。
// ノードの種類とつなぎ方：
//   公理（全ゲーム共通の前提。表示だけで編集・削除できない）・集合（カードの種類・マナの色・タグの集合。1つだけ、削除できない）
//   はどこにもつながない
//   ルール ──▶ ゾーン（上から順に Rules.zones の順番）
//   カード ──▶ 効果（「発動」「無効（永続）」「攻撃力の変化（永続）」「守備力の変化（永続）」）
//   発動 ──▶ 動き（「破壊」「手札に戻す」「ドロー」「ダメージ」「回復」「カードへのダメージ」。上から順に行う）
//   破壊・手札に戻す・カードへのダメージ・無効・攻撃力の変化・守備力の変化 ──▶ 範囲（ちょうど1つ）
using System.Collections.Generic;
using System.Linq;

namespace CardGen
{
    public enum NodeKind { Rules, Zone, Card, Activate, Negate, Destroy, Bounce, Draw, Selector, Damage, Heal, Boost, Axioms, Sets, Toughen, Strike }

    /// <summary>公理：すべてのゲームに共通の前提（中間表現には書かず、Lean のモデルが前提にする）</summary>
    public static class Axioms
    {
        public static readonly string[] Lines =
        {
            "プレイヤーは自分と相手の2人",
            "相手のフィールドは自分のフィールドを逆さまにした形（ゾーンは1人分だけ書く）",
            $"盤面は最大 50×50 のマス目（ここでは {Grid.Size}×{Grid.Size}。相手のマスは中心のマス（{Grid.Size / 2}, {Grid.Size / 2}）について点対称）",
            "マスの並びは縦と横の2本の序列で、大小の比較と「1つ隣」だけを使う",
            "2人で共有するマスはない",
            "カードの持ち主と、コントロールするプレイヤーは同じ",
        };
    }

    /// <summary>集合のノードの中身：カードの種類・マナの色・タグの集合</summary>
    public sealed class SetsData
    {
        public List<string> CardTypes = new List<string>();
        public List<string> ManaColors = new List<string>();
        public List<TagSet> TagSets = new List<TagSet>();
    }

    /// <summary>ルールのノードの中身（ゾーンはつないだノードから作る。カードの種類とマナの色は集合のノード）</summary>
    public sealed class RulesData
    {
        public int DeckSize;
        public int HandSize;
        public int Life;
        public List<string> Fighters = new List<string>();
        public int SummonsPerTurn = 1;
        public int DrawPerTurn = 1;
        public bool FirstTurnDraw;
        public bool FirstTurnAttack;
        public List<PlaceLimit> PlaceLimits = new List<PlaceLimit>();
        public bool AttackTaps;
        public bool SummoningSickness;
        public bool Blocking;
        public List<string> Instants = new List<string>();
        public bool Stack;
    }

    /// <summary>カードのノードの中身（効果はつないだノードから作る）</summary>
    public sealed class CardData
    {
        public string Name = "";
        public string Type = "";
        public List<string> Tags = new List<string>();
        public int Attack;
        public int Defense;
        public int Cost;
        public List<string> ColorCost = new List<string>();
        public int Mana;
        public string ManaColor = "";
        public List<string> ManaChoice = new List<string>();
    }

    public sealed class Node
    {
        public int Id;
        public NodeKind Kind;
        public float X, Y;
        public RulesData Rules;
        public SetsData Sets;
        public Zone Zone;
        public CardData Card;
        public Selector Selector;
        /// <summary>ドローの枚数（Draw のノード）</summary>
        public int DrawCount = 1;
        /// <summary>ダメージ・回復の量、攻撃力・守備力の変化の量（Damage・Heal・Strike・Boost・Toughen のノード）</summary>
        public int Amount = 500;

        public static Node Make(int id, NodeKind kind, float x, float y)
        {
            var n = new Node { Id = id, Kind = kind, X = x, Y = y };
            switch (kind)
            {
                case NodeKind.Rules: n.Rules = new RulesData(); break;
                case NodeKind.Sets: n.Sets = new SetsData(); break;
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
            NodeKind.Activate => "発動",
            NodeKind.Negate => "無効（永続）",
            NodeKind.Destroy => "破壊",
            NodeKind.Bounce => "手札に戻す",
            NodeKind.Draw => "ドロー",
            NodeKind.Damage => "ダメージ",
            NodeKind.Heal => "回復",
            NodeKind.Boost => "攻撃力の変化（永続）",
            NodeKind.Toughen => "守備力の変化（永続）",
            NodeKind.Strike => "カードへのダメージ",
            NodeKind.Axioms => "公理",
            NodeKind.Sets => "集合",
            _ => "範囲",
        };

        /// <summary>動き（発動の下につなぐノード）か</summary>
        public static bool IsAction(NodeKind k) =>
            k == NodeKind.Destroy || k == NodeKind.Bounce || k == NodeKind.Draw || k == NodeKind.Damage || k == NodeKind.Heal ||
            k == NodeKind.Strike;

        /// <summary>カードの下につなぐ効果のノードか</summary>
        public static bool IsEffect(NodeKind k) =>
            k == NodeKind.Activate || k == NodeKind.Negate || k == NodeKind.Boost || k == NodeKind.Toughen;

        /// <summary>範囲を1つつなぐノードか</summary>
        public static bool TakesSelector(NodeKind k) =>
            k == NodeKind.Destroy || k == NodeKind.Bounce || k == NodeKind.Negate || k == NodeKind.Boost ||
            k == NodeKind.Toughen || k == NodeKind.Strike;

        /// <summary>右側（つなぎ元）の丸を持つか</summary>
        public static bool HasOutput(NodeKind k) =>
            k == NodeKind.Rules || k == NodeKind.Card || k == NodeKind.Activate || TakesSelector(k);

        /// <summary>左側（つなぎ先）の丸を持つか</summary>
        public static bool HasInput(NodeKind k) => k != NodeKind.Rules && k != NodeKind.Card && !IsFixed(k);

        /// <summary>削除できず、追加もしないノード（公理・集合。どのゲームにも1つずつある）</summary>
        public static bool IsFixed(NodeKind k) => k == NodeKind.Axioms || k == NodeKind.Sets;

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

        /// <summary>from から to へつないでよいか</summary>
        public static bool CanConnect(NodeKind from, NodeKind to) =>
            (from == NodeKind.Rules && to == NodeKind.Zone) ||
            (from == NodeKind.Card && Node.IsEffect(to)) ||
            (from == NodeKind.Activate && Node.IsAction(to)) ||
            (Node.TakesSelector(from) && to == NodeKind.Selector);

        /// <summary>つなぐ。入る側はつなぎ元を1つしか持てない。範囲を取るノードは範囲を1つしか持てない</summary>
        public bool Connect(int from, int to)
        {
            var a = Find(from);
            var b = Find(to);
            if (a == null || b == null || !CanConnect(a.Kind, b.Kind)) return false;
            Edges.RemoveAll(e => e.To == to);
            if (Node.TakesSelector(a.Kind)) Edges.RemoveAll(e => e.From == from);
            Edges.Add(new Edge(from, to));
            return true;
        }

        public void Remove(int id)
        {
            var n = Find(id);
            if (n == null || Node.IsFixed(n.Kind)) return;
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
            var problems = structure;
            var rulesNodes = Nodes.Where(n => n.Kind == NodeKind.Rules).ToList();
            var rules = new Rules();
            if (rulesNodes.Count == 0) structure.Add("ルールのノードがありません");
            if (rulesNodes.Count > 1) structure.Add("ルールのノードは1つだけにしてください");
            var setsNode = Nodes.FirstOrDefault(n => n.Kind == NodeKind.Sets);
            if (setsNode == null) structure.Add("集合のノードがありません");
            else
            {
                rules.CardTypes = setsNode.Sets.CardTypes.ToList();
                rules.ManaColors = setsNode.Sets.ManaColors.ToList();
                rules.TagSets = setsNode.Sets.TagSets.Select(t => new TagSet { Name = t.Name, Values = t.Values.ToList() }).ToList();
            }
            if (rulesNodes.Count > 0)
            {
                var r = rulesNodes[0];
                rules.DeckSize = r.Rules.DeckSize;
                rules.HandSize = r.Rules.HandSize;
                rules.Life = r.Rules.Life;
                rules.Fighters = r.Rules.Fighters.ToList();
                rules.SummonsPerTurn = r.Rules.SummonsPerTurn;
                rules.DrawPerTurn = r.Rules.DrawPerTurn;
                rules.FirstTurnDraw = r.Rules.FirstTurnDraw;
                rules.FirstTurnAttack = r.Rules.FirstTurnAttack;
                rules.PlaceLimits = r.Rules.PlaceLimits.Select(l => new PlaceLimit { Types = l.Types.ToList(), Count = l.Count }).ToList();
                rules.AttackTaps = r.Rules.AttackTaps;
                rules.SummoningSickness = r.Rules.SummoningSickness;
                rules.Blocking = r.Rules.Blocking;
                rules.Instants = r.Rules.Instants.ToList();
                rules.Stack = r.Rules.Stack;
                rules.Zones = Children(r).Select(z => z.Zone).ToList();
            }
            foreach (var z in Nodes.Where(n => n.Kind == NodeKind.Zone && Parents(n).Count == 0))
                structure.Add($"ゾーン「{z.Zone.Name}」がルールにつながっていません");

            var cards = new List<Card>();
            foreach (var c in Nodes.Where(n => n.Kind == NodeKind.Card).OrderBy(n => n.Y).ThenBy(n => n.X))
            {
                var card = new Card { Name = c.Card.Name, Type = c.Card.Type, Tags = c.Card.Tags.ToList(),
                                      Attack = c.Card.Attack, Defense = c.Card.Defense, Cost = c.Card.Cost, Mana = c.Card.Mana,
                                      ColorCost = c.Card.ColorCost.ToList(), ManaColor = c.Card.ManaColor,
                                      ManaChoice = c.Card.ManaChoice.ToList() };
                Selector SelectorOf(Node n, string what)
                {
                    var s = Children(n).FirstOrDefault();
                    if (s == null) problems.Add($"カード「{c.Card.Name}」の{what}に、範囲がつながっていません");
                    return s?.Selector;
                }
                foreach (var e in Children(c))
                {
                    if (e.Kind == NodeKind.Negate)
                    {
                        var s = SelectorOf(e, "無効の効果");
                        if (s != null) card.Effects.Add(new Negate(s));
                        continue;
                    }
                    if (e.Kind == NodeKind.Boost)
                    {
                        var s = SelectorOf(e, "攻撃力の変化");
                        if (s != null) card.Effects.Add(new Boost(s, e.Amount));
                        continue;
                    }
                    if (e.Kind == NodeKind.Toughen)
                    {
                        var s = SelectorOf(e, "守備力の変化");
                        if (s != null) card.Effects.Add(new Toughen(s, e.Amount));
                        continue;
                    }
                    var actions = new List<Action>();
                    foreach (var a in Children(e))
                    {
                        if (a.Kind == NodeKind.Draw) { actions.Add(new DrawCards(a.DrawCount)); continue; }
                        if (a.Kind == NodeKind.Damage) { actions.Add(new Damage(a.Amount)); continue; }
                        if (a.Kind == NodeKind.Heal) { actions.Add(new Heal(a.Amount)); continue; }
                        if (a.Kind == NodeKind.Strike)
                        {
                            var st = SelectorOf(a, "カードへのダメージ");
                            if (st != null) actions.Add(new Strike(st, a.Amount));
                            continue;
                        }
                        var s = SelectorOf(a, a.Kind == NodeKind.Destroy ? "破壊" : "手札に戻す動き");
                        if (s == null) continue;
                        actions.Add(a.Kind == NodeKind.Destroy ? (Action)new Destroy(s) : new Bounce(s));
                    }
                    card.Effects.Add(new Activated(actions));
                }
                cards.Add(card);
            }
            foreach (var e in Nodes.Where(n => Node.IsEffect(n.Kind) && Parents(n).Count == 0))
                structure.Add($"{Node.KindLabel(e.Kind)}のノードがカードにつながっていません");
            foreach (var a in Nodes.Where(n => Node.IsAction(n.Kind) && Parents(n).Count == 0))
                structure.Add($"{Node.KindLabel(a.Kind)}のノードが発動につながっていません");
            foreach (var s in Nodes.Where(n => n.Kind == NodeKind.Selector && Parents(n).Count == 0))
                structure.Add("範囲のノードがつながっていません");

            return new Game { Rules = rules, Cards = cards };
        }

        /// <summary>公理と集合のノードの高さの分、ほかのノードを下げる量</summary>
        public const float FixedHeight = 600;

        /// <summary>公理と集合のノードを左上に加え、ほかのノードをその分下げる。集合のノードを返す</summary>
        public static Node AddFixedNodes(GraphDoc doc)
        {
            foreach (var n in doc.Nodes) n.Y += FixedHeight;
            var id = doc.NextId;
            var ax = Node.Make(id, NodeKind.Axioms, 40, 40);
            var sets = Node.Make(id + 1, NodeKind.Sets, 40, 330);
            doc.Nodes.Add(ax);
            doc.Nodes.Add(sets);
            return sets;
        }

        /// <summary>新しいゲーム：公理・集合・ルールのノードだけ</summary>
        public static GraphDoc New()
        {
            var doc = new GraphDoc();
            doc.Nodes.Add(Node.Make(1, NodeKind.Rules, 40, 40));
            AddFixedNodes(doc);
            return doc;
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
            const float colCard = 40, colEffect = 300, colAction = 560, colSelector = 820;

            var r = Add(NodeKind.Rules, colCard, 40);
            r.Rules.DeckSize = g.Rules.DeckSize;
            r.Rules.HandSize = g.Rules.HandSize;
            r.Rules.Life = g.Rules.Life;
            r.Rules.Fighters = g.Rules.Fighters.ToList();
            r.Rules.SummonsPerTurn = g.Rules.SummonsPerTurn;
            r.Rules.DrawPerTurn = g.Rules.DrawPerTurn;
            r.Rules.FirstTurnDraw = g.Rules.FirstTurnDraw;
            r.Rules.FirstTurnAttack = g.Rules.FirstTurnAttack;
            r.Rules.PlaceLimits = g.Rules.PlaceLimits.Select(l => new PlaceLimit { Types = l.Types.ToList(), Count = l.Count }).ToList();
            r.Rules.AttackTaps = g.Rules.AttackTaps;
            r.Rules.SummoningSickness = g.Rules.SummoningSickness;
            r.Rules.Blocking = g.Rules.Blocking;
            r.Rules.Instants = g.Rules.Instants.ToList();
            r.Rules.Stack = g.Rules.Stack;
            float zy = 40;
            foreach (var z in g.Rules.Zones)
            {
                var zn = Add(NodeKind.Zone, colEffect, zy);
                zn.Zone = z;
                doc.Edges.Add(new Edge(r.Id, zn.Id));
                zy += 110;
            }

            float y = Max(zy + 40, 520);
            foreach (var c in g.Cards)
            {
                var cn = Add(NodeKind.Card, colCard, y);
                cn.Card = new CardData { Name = c.Name, Type = c.Type, Tags = c.Tags.ToList(), Attack = c.Attack, Defense = c.Defense,
                                     Cost = c.Cost, Mana = c.Mana, ColorCost = c.ColorCost.ToList(), ManaColor = c.ManaColor,
                                     ManaChoice = c.ManaChoice.ToList() };
                float ey = y;
                foreach (var e in c.Effects)
                {
                    if (e is Negate neg)
                    {
                        var en = Add(NodeKind.Negate, colEffect, ey);
                        doc.Edges.Add(new Edge(cn.Id, en.Id));
                        var sn = Add(NodeKind.Selector, colAction, ey);
                        sn.Selector = neg.Target;
                        doc.Edges.Add(new Edge(en.Id, sn.Id));
                        ey += 130;
                        continue;
                    }
                    if (e is Boost || e is Toughen)
                    {
                        var bn = Add(e is Boost ? NodeKind.Boost : NodeKind.Toughen, colEffect, ey);
                        bn.Amount = e is Boost bo ? bo.Amount : ((Toughen)e).Amount;
                        doc.Edges.Add(new Edge(cn.Id, bn.Id));
                        var sn = Add(NodeKind.Selector, colAction, ey);
                        sn.Selector = e is Boost bo2 ? bo2.Target : ((Toughen)e).Target;
                        doc.Edges.Add(new Edge(bn.Id, sn.Id));
                        ey += 130;
                        continue;
                    }
                    var act = (Activated)e;
                    var an = Add(NodeKind.Activate, colEffect, ey);
                    doc.Edges.Add(new Edge(cn.Id, an.Id));
                    float ay = ey;
                    foreach (var a in act.Actions)
                    {
                        switch (a)
                        {
                            case DrawCards d:
                                var dn = Add(NodeKind.Draw, colAction, ay);
                                dn.DrawCount = d.Count;
                                doc.Edges.Add(new Edge(an.Id, dn.Id));
                                ay += 90;
                                break;
                            case Damage _:
                            case Heal _:
                                var hn = Add(a is Damage ? NodeKind.Damage : NodeKind.Heal, colAction, ay);
                                hn.Amount = a is Damage dmg ? dmg.Amount : ((Heal)a).Amount;
                                doc.Edges.Add(new Edge(an.Id, hn.Id));
                                ay += 90;
                                break;
                            case Destroy _:
                            case Bounce _:
                            case Strike _:
                                var target = a is Destroy de ? de.Target : a is Bounce bou ? bou.Target : ((Strike)a).Target;
                                var xn = Add(a is Destroy ? NodeKind.Destroy : a is Bounce ? NodeKind.Bounce : NodeKind.Strike, colAction, ay);
                                if (a is Strike sk) xn.Amount = sk.Amount;
                                doc.Edges.Add(new Edge(an.Id, xn.Id));
                                var sn = Add(NodeKind.Selector, colSelector, ay);
                                sn.Selector = target;
                                doc.Edges.Add(new Edge(xn.Id, sn.Id));
                                ay += 130;
                                break;
                        }
                    }
                    ey = Max(ey + 90, ay);
                }
                y = Max(y + 110, ey + 20);
            }
            var sets = AddFixedNodes(doc);
            sets.Sets.CardTypes = g.Rules.CardTypes.ToList();
            sets.Sets.ManaColors = g.Rules.ManaColors.ToList();
            sets.Sets.TagSets = g.Rules.TagSets.Select(t => new TagSet { Name = t.Name, Values = t.Values.ToList() }).ToList();
            return doc;
        }

        static float Max(float a, float b) => a > b ? a : b;
    }
}
