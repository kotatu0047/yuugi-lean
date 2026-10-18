using System.Linq;
using UnityEngine;
using UnityEngine.UIElements;

namespace CardGen.App
{
    /// <summary>キャンバス上のノード1つ</summary>
    public sealed class NodeView : VisualElement
    {
        public const float Width = 220f;
        public const float HeaderHeight = 28f;

        public readonly Node Node;
        readonly Label kindLabel;
        readonly Label titleLabel;
        readonly Label body;
        public readonly VisualElement InPort;
        public readonly VisualElement OutPort;

        public static Color KindColor(NodeKind k) => k switch
        {
            NodeKind.Rules => new Color(0.55f, 0.35f, 0.75f),
            NodeKind.Zone => new Color(0.25f, 0.50f, 0.75f),
            NodeKind.Card => new Color(0.80f, 0.55f, 0.20f),
            NodeKind.Activate => new Color(0.70f, 0.40f, 0.25f),
            NodeKind.Destroy => new Color(0.75f, 0.30f, 0.30f),
            NodeKind.Bounce => new Color(0.30f, 0.55f, 0.70f),
            NodeKind.Draw => new Color(0.55f, 0.50f, 0.25f),
            NodeKind.Negate => new Color(0.30f, 0.60f, 0.40f),
            NodeKind.Boost => new Color(0.25f, 0.55f, 0.55f),
            NodeKind.Damage => new Color(0.80f, 0.35f, 0.50f),
            NodeKind.Heal => new Color(0.35f, 0.65f, 0.35f),
            _ => new Color(0.45f, 0.45f, 0.50f),
        };

        public NodeView(Node node)
        {
            Node = node;
            style.position = Position.Absolute;
            style.width = Width;
            style.backgroundColor = new Color(0.17f, 0.17f, 0.19f, 0.97f);
            SetBorder(1, new Color(0.3f, 0.3f, 0.33f));
            style.borderTopLeftRadius = style.borderTopRightRadius = style.borderBottomLeftRadius = style.borderBottomRightRadius = 6;

            var header = new VisualElement { name = "header" };
            header.style.height = HeaderHeight;
            header.style.flexDirection = FlexDirection.Row;
            header.style.alignItems = Align.Center;
            header.style.paddingLeft = 14;
            header.style.paddingRight = 14;
            header.style.backgroundColor = KindColor(node.Kind);
            header.style.borderTopLeftRadius = header.style.borderTopRightRadius = 5;
            kindLabel = new Label(Node.KindLabel(node.Kind));
            kindLabel.style.fontSize = 11;
            kindLabel.style.color = new Color(1, 1, 1, 0.8f);
            kindLabel.style.marginRight = 6;
            titleLabel = new Label();
            titleLabel.style.unityFontStyleAndWeight = FontStyle.Bold;
            titleLabel.style.color = Color.white;
            titleLabel.style.overflow = Overflow.Hidden;
            titleLabel.style.flexShrink = 1;
            header.Add(kindLabel);
            header.Add(titleLabel);
            Add(header);

            body = new Label();
            body.style.whiteSpace = WhiteSpace.Normal;
            body.style.paddingLeft = 10;
            body.style.paddingRight = 10;
            body.style.paddingTop = 6;
            body.style.paddingBottom = 8;
            body.style.fontSize = 12;
            body.style.color = new Color(0.85f, 0.85f, 0.88f);
            Add(body);

            InPort = MakePort(left: true);
            OutPort = MakePort(left: false);
            if (Node.HasInput(node.Kind)) Add(InPort);
            if (Node.HasOutput(node.Kind)) Add(OutPort);

            Refresh();
        }

        VisualElement MakePort(bool left)
        {
            var p = new VisualElement { name = left ? "in-port" : "out-port" };
            p.style.position = Position.Absolute;
            p.style.width = 14;
            p.style.height = 14;
            p.style.top = HeaderHeight / 2 - 7;
            if (left) p.style.left = -7; else p.style.right = -7;
            p.style.backgroundColor = new Color(0.9f, 0.9f, 0.92f);
            p.style.borderTopLeftRadius = p.style.borderTopRightRadius = p.style.borderBottomLeftRadius = p.style.borderBottomRightRadius = 7;
            p.style.borderLeftWidth = p.style.borderRightWidth = p.style.borderTopWidth = p.style.borderBottomWidth = 2;
            var c = new Color(0.15f, 0.15f, 0.17f);
            p.style.borderLeftColor = p.style.borderRightColor = p.style.borderTopColor = p.style.borderBottomColor = c;
            return p;
        }

        void SetBorder(float w, Color c)
        {
            style.borderLeftWidth = style.borderRightWidth = style.borderTopWidth = style.borderBottomWidth = w;
            style.borderLeftColor = style.borderRightColor = style.borderTopColor = style.borderBottomColor = c;
        }

        public void SetSelected(bool on) =>
            SetBorder(on ? 2 : 1, on ? new Color(1f, 0.85f, 0.3f) : new Color(0.3f, 0.3f, 0.33f));

        public void SetProblem(bool on) => style.backgroundColor = on
            ? new Color(0.30f, 0.14f, 0.14f, 0.97f) : new Color(0.17f, 0.17f, 0.19f, 0.97f);

        /// <summary>位置と表示を中身に合わせる</summary>
        public void Refresh()
        {
            style.left = Node.X;
            style.top = Node.Y;
            titleLabel.text = Node.Kind == NodeKind.Zone || Node.Kind == NodeKind.Card ? Node.Title : "";
            body.text = Summary(Node);
        }

        static string List(System.Collections.Generic.IEnumerable<string> l, string empty = "（なし）")
        {
            var s = string.Join("・", l);
            return s.Length == 0 ? empty : s;
        }

        static string Summary(Node n) => n.Kind switch
        {
            NodeKind.Rules =>
                $"カードの種類：{List(n.Rules.CardTypes)}\nデッキ {n.Rules.DeckSize}枚・初期手札 {n.Rules.HandSize}枚\n" +
                $"ライフ {n.Rules.Life}・戦闘できる種類：{List(n.Rules.Fighters)}\n" +
                $"召喚 {(n.Rules.SummonsPerTurn == 0 ? "制限なし" : $"1ターン{n.Rules.SummonsPerTurn}回")}・ドロー {n.Rules.DrawPerTurn}枚" +
                (n.Rules.FirstTurnDraw ? "・先攻1ターン目も引く" : "") + (n.Rules.FirstTurnAttack ? "・先攻1ターン目も攻撃" : ""),
            NodeKind.Zone =>
                $"{n.Zone.Count}マス・{(n.Zone.Capacity == Capacity.One ? "1枚まで" : "何枚でも")}・" +
                $"{(n.Zone.Role == ZoneRole.Deck ? "デッキ" : n.Zone.Role == ZoneRole.Grave ? "墓地" : n.Zone.OnField ? "フィールド上" : "フィールド外")}\n" +
                $"置ける種類：{List(n.Zone.Admits)}",
            NodeKind.Card =>
                $"種類：{(n.Card.Type.Length == 0 ? "（未設定）" : n.Card.Type)}" + (n.Card.Tags.Count > 0 ? $"\nタグ：{List(n.Card.Tags)}" : "") +
                (n.Card.Attack > 0 || n.Card.Defense > 0 ? $"\n攻撃力 {n.Card.Attack}・守備力 {n.Card.Defense}" : ""),
            NodeKind.Activate => "発動し、つないだ動きを上から順に行う",
            NodeKind.Destroy => "つないだ範囲のカードをすべて破壊し、持ち主の墓地へ送る",
            NodeKind.Bounce => "つないだ範囲のカードをすべて持ち主の手札に戻す",
            NodeKind.Draw => $"発動したプレイヤーがカードを {n.DrawCount} 枚引く",
            NodeKind.Negate => "表側表示で存在する限り、つないだ範囲のカードの効果を無効にする",
            NodeKind.Boost => $"表側表示で存在する限り、つないだ範囲のカードの攻撃力を {(n.Amount >= 0 ? "+" : "")}{n.Amount}",
            NodeKind.Damage => $"相手に {n.Amount} のダメージを与える",
            NodeKind.Heal => $"発動したプレイヤーのライフを {n.Amount} 回復する",
            _ => SelectorSummary(n.Selector),
        };

        public static string SelectorSummary(Selector s)
        {
            var side = s.Side == Side.Self ? "自分の" : s.Side == Side.Opp ? "相手の" : "お互いの";
            var parts = $"{side}{(s.FaceUpOnly ? "表側表示の" : "")}{List(s.Types, "（種類なし）")}";
            if (s.Tags.Count > 0) parts += $"（{List(s.Tags)}）";
            if (s.ExcludeSelf) parts += "\nこのカード自身を除く";
            return parts;
        }
    }
}
