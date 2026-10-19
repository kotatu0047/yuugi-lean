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

        public static Color KindColor(NodeKind k) => Theme.Kind(k);

        bool selected, problem;
        readonly VisualElement brackets;
        // 外側の光彩（選んでいればアンバーで明滅、問題があれば赤）
        readonly VisualElement glow;
        float pulse = 1;
        const float GlowSize = 12;

        public NodeView(Node node)
        {
            Node = node;
            var kc = KindColor(node.Kind);
            style.position = Position.Absolute;
            style.width = Width;
            // 公理・集合は文が長いので広くする（つなぐ丸はない）
            if (Node.IsFixed(node.Kind)) style.width = 320;
            Theme.Round(style, 2);
            // 四隅のブラケット：選んでいればアンバー、問題があれば赤、ふだんは種類の色
            glow = new VisualElement { name = "glow", pickingMode = PickingMode.Ignore };
            glow.style.position = Position.Absolute;
            glow.style.left = glow.style.top = -GlowSize;
            glow.style.right = glow.style.bottom = -GlowSize;
            glow.generateVisualContent += DrawGlow;
            Add(glow);
            Paint();

            var header = new VisualElement { name = "header" };
            header.style.height = HeaderHeight;
            header.style.flexDirection = FlexDirection.Row;
            header.style.alignItems = Align.Center;
            header.style.paddingLeft = 12;
            header.style.paddingRight = 12;
            header.style.backgroundColor = Theme.Alpha(kc, 0.16f);
            header.style.borderLeftWidth = 3;
            header.style.borderLeftColor = kc;
            header.style.borderBottomWidth = 1;
            header.style.borderBottomColor = Theme.Alpha(kc, 0.55f);
            kindLabel = new Label(Node.KindLabel(node.Kind));
            kindLabel.style.fontSize = 11;
            kindLabel.style.color = kc;
            kindLabel.style.unityFontStyleAndWeight = FontStyle.Bold;
            kindLabel.style.marginRight = 6;
            titleLabel = new Label();
            titleLabel.style.unityFontStyleAndWeight = FontStyle.Bold;
            titleLabel.style.color = Theme.Bright;
            titleLabel.style.overflow = Overflow.Hidden;
            titleLabel.style.flexShrink = 1;
            titleLabel.style.flexGrow = 1;
            header.Add(kindLabel);
            header.Add(titleLabel);
            var id = Theme.Tag($"#{node.Id:D3}", Theme.Alpha(kc, 0.65f), 9);
            id.style.flexShrink = 0;
            header.Add(id);
            Add(header);

            body = new Label();
            body.style.whiteSpace = WhiteSpace.Normal;
            body.style.paddingLeft = 10;
            body.style.paddingRight = 10;
            body.style.paddingTop = 6;
            body.style.paddingBottom = 8;
            body.style.fontSize = 12;
            body.style.color = Theme.Text;
            Add(body);

            InPort = MakePort(left: true);
            OutPort = MakePort(left: false);
            if (Node.HasInput(node.Kind)) Add(InPort);
            if (Node.HasOutput(node.Kind)) Add(OutPort);
            brackets = Theme.BracketsOverlay(() => selected ? Theme.Alpha(Theme.Amber, 0.45f + 0.55f * pulse)
                : problem ? Theme.Red : Theme.Alpha(kc, 0.9f), 10, 2f);
            Add(brackets);

            Refresh();
        }

        VisualElement MakePort(bool left)
        {
            // つなぐ丸：中が暗く、種類の色の輪（ひし形に回して HUD らしくする）
            var kc = KindColor(Node.Kind);
            var p = new VisualElement { name = left ? "in-port" : "out-port" };
            p.style.position = Position.Absolute;
            p.style.width = 12;
            p.style.height = 12;
            p.style.top = HeaderHeight / 2 - 6;
            if (left) p.style.left = -7; else p.style.right = -7;
            p.style.backgroundColor = Theme.Deep;
            p.style.rotate = new Rotate(45);
            Theme.Border(p.style, 2, kc);
            var core = new VisualElement { pickingMode = PickingMode.Ignore };
            core.style.position = Position.Absolute;
            core.style.left = core.style.top = 2;
            core.style.width = core.style.height = 4;
            core.style.backgroundColor = kc;
            p.Add(core);
            return p;
        }

        /// <summary>選んでいるノードの明滅を進める（t：秒。1.6 秒で1周）</summary>
        public void Pulse(float t)
        {
            pulse = 0.5f + 0.5f * Mathf.Sin(t * Mathf.PI * 2 / 1.6f);
            glow.MarkDirtyRepaint();
            brackets.MarkDirtyRepaint();
        }

        /// <summary>ノードの外側に、だんだん薄くなる線を重ねて光彩にする（ノードの内側には描かない）</summary>
        void DrawGlow(MeshGenerationContext ctx)
        {
            if (!selected && !problem) return;
            var c = selected ? Theme.Amber : Theme.Red;
            float strength = selected ? 0.12f + 0.2f * pulse : 0.14f;
            var w = glow.layout.width;
            var h = glow.layout.height;
            if (float.IsNaN(w) || float.IsNaN(h)) return;
            var p = ctx.painter2D;
            p.lineWidth = 1.5f;
            for (int i = 1; i <= (int)GlowSize; i++)
            {
                float f = 1f - (i - 1) / GlowSize;
                p.strokeColor = Theme.Alpha(c, strength * f * f);
                float x0 = GlowSize - i, y0 = GlowSize - i, x1 = w - GlowSize + i, y1 = h - GlowSize + i;
                p.BeginPath();
                p.MoveTo(new Vector2(x0, y0));
                p.LineTo(new Vector2(x1, y0));
                p.LineTo(new Vector2(x1, y1));
                p.LineTo(new Vector2(x0, y1));
                p.ClosePath();
                p.Stroke();
            }
        }

        void Paint()
        {
            style.backgroundColor = problem ? Theme.Alpha(Theme.Red, 0.14f) : Theme.Panel;
            Theme.Border(style, 1, selected ? Theme.Amber : problem ? Theme.Alpha(Theme.Red, 0.8f) : Theme.Line);
            brackets?.MarkDirtyRepaint();
            glow?.MarkDirtyRepaint();
        }

        public void SetSelected(bool on) { selected = on; pulse = 1; Paint(); }

        public void SetProblem(bool on) { problem = on; Paint(); }

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
                $"デッキ {n.Rules.DeckSize}枚・初期手札 {n.Rules.HandSize}枚\n" +
                $"ライフ {n.Rules.Life}・戦闘できる種類：{List(n.Rules.Fighters)}\n" +
                $"召喚 {(n.Rules.SummonsPerTurn == 0 ? "制限なし" : $"1ターン{n.Rules.SummonsPerTurn}回")}・ドロー {n.Rules.DrawPerTurn}枚" +
                (n.Rules.FirstTurnDraw ? "・先攻1ターン目も引く" : "") + (n.Rules.FirstTurnAttack ? "・先攻1ターン目も攻撃" : "") +
                (n.Rules.PlaceLimits.Count > 0 ? $"\n上限：{string.Join("・", n.Rules.PlaceLimits.Select(l => $"{string.Join("+", l.Types)} {l.Count}枚"))}" : "") +
                (n.Rules.AttackTaps ? "\n攻撃でタップ" : "") + (n.Rules.SummoningSickness ? (n.Rules.AttackTaps ? "・" : "\n") + "召喚酔い" : "") +
                (n.Rules.Blocking ? "\nMTG 式の戦闘（ブロック）" : "") +
                (n.Rules.Instants.Count > 0 ? $"\nいつでも置ける：{List(n.Rules.Instants)}" : "") +
                (n.Rules.Stack ? "\nスタック" : "") +
                "",
            NodeKind.Zone =>
                $"{n.Zone.Count}マス・{(n.Zone.Capacity == Capacity.One ? "1枚まで" : "何枚でも")}・" +
                $"{(n.Zone.Role == ZoneRole.Deck ? "デッキ" : n.Zone.Role == ZoneRole.Grave ? "墓地" : n.Zone.OnField ? "フィールド上" : "フィールド外")}\n" +
                $"置ける種類：{List(n.Zone.Admits)}" +
                (n.Zone.Cells.Count > 0 ? $"\nマス：{Inspector.CellsText(n.Zone.Cells.Take(3))}{(n.Zone.Cells.Count > 3 ? " …" : "")}" : ""),
            NodeKind.Card =>
                $"種類：{(n.Card.Type.Length == 0 ? "（未設定）" : n.Card.Type)}" + (n.Card.Tags.Count > 0 ? $"\nタグ：{List(n.Card.Tags)}" : "") +
                (n.Card.Attack > 0 || n.Card.Defense > 0 ? $"\n攻撃力 {n.Card.Attack}・守備力 {n.Card.Defense}" : "") +
                (n.Card.Trample ? "・トランプル" : "") + (n.Card.Flying ? "・飛行" : "") + (n.Card.Reach ? "・到達" : "") +
                (n.Card.Mana > 0 ? $"\nタップで{(n.Card.ManaChoice.Count > 0 ? string.Join("か", n.Card.ManaChoice) : n.Card.ManaColor == "" ? "無色" : n.Card.ManaColor)}マナ {n.Card.Mana}" : "") +
                (n.Card.Cost > 0 || n.Card.ColorCost.Count > 0 ? $"\nコスト {(n.Card.Cost > 0 ? n.Card.Cost.ToString() : "")}{(n.Card.Cost > 0 && n.Card.ColorCost.Count > 0 ? "＋" : "")}{string.Concat(n.Card.ColorCost)}" : ""),
            NodeKind.Axioms => "編集できません\n" + string.Join("\n", Axioms.Lines.Select((l, i) => $"{i + 1}. {l}")),
            NodeKind.Sets =>
                $"カードの種類：{List(n.Sets.CardTypes)}" +
                (n.Sets.ManaColors.Count > 0 ? $"\nマナの色：{List(n.Sets.ManaColors)}" : "") +
                string.Concat(n.Sets.TagSets.Select(t => $"\n{t.Name}：{List(t.Values)}")),
            NodeKind.Activate => "発動し、つないだ動きを上から順に行う",
            NodeKind.Destroy => "つないだ範囲のカードをすべて破壊し、持ち主の墓地へ送る",
            NodeKind.Bounce => "つないだ範囲のカードをすべて持ち主の手札に戻す",
            NodeKind.Draw => $"発動したプレイヤーがカードを {n.DrawCount} 枚引く",
            NodeKind.Negate => "表側表示で存在する限り、つないだ範囲のカードの効果を無効にする",
            NodeKind.Boost => $"表側表示で存在する限り、つないだ範囲のカードの攻撃力を {(n.Amount >= 0 ? "+" : "")}{n.Amount}",
            NodeKind.Toughen => $"表側表示で存在する限り、つないだ範囲のカードの守備力を {(n.Amount >= 0 ? "+" : "")}{n.Amount}",
            NodeKind.Strike => $"つないだ範囲の戦闘できるカードすべてに {n.Amount} のダメージ（ターンの終わりまで残る）",
            NodeKind.Pump => $"つないだ範囲の戦闘できるカードの攻撃力 {(n.Amount >= 0 ? "+" : "")}{n.Amount}・守備力 {(n.Amount2 >= 0 ? "+" : "")}{n.Amount2}（ターンの終わりまで）",
            NodeKind.Counter => "つないだ範囲の、フィールド上でないカード（スタックの呪文など）を打ち消す",
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
            if (s.Near == Near.Adjacent) parts = "隣のマスの" + parts;
            if (s.Near == Near.SameColumn) parts = "同じ縦列の" + parts;
            if (s.Target) parts = "対象1枚：" + parts;
            return parts;
        }
    }
}
