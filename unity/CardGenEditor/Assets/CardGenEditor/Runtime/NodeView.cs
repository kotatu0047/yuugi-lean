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
        // 問題があるときの演出：ノードの上に浮かぶ警告テープ（流れる斜めの縞）、見出しの「FAULT」の札、下の問題の文
        readonly Label idTag;
        readonly VisualElement faultChip;
        readonly VisualElement tape;
        readonly VisualElement tapeStripes;
        readonly VisualElement faultBox;
        readonly Label faultText;
        float tapePhase;

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
            idTag = Theme.Tag($"#{node.Id:D3}", Theme.Alpha(kc, 0.65f), 9);
            idTag.style.flexShrink = 0;
            header.Add(idTag);
            faultChip = new VisualElement { pickingMode = PickingMode.Ignore };
            faultChip.style.flexShrink = 0;
            faultChip.style.display = DisplayStyle.None;
            faultChip.style.backgroundColor = Theme.Red;
            faultChip.style.paddingLeft = 5;
            faultChip.style.paddingRight = 5;
            faultChip.style.paddingTop = 1;
            faultChip.style.paddingBottom = 1;
            faultChip.Add(Theme.Tag("!! fault", Theme.Void, 9));
            header.Add(faultChip);
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

            faultBox = new VisualElement { pickingMode = PickingMode.Ignore };
            faultBox.style.display = DisplayStyle.None;
            faultBox.style.flexDirection = FlexDirection.Row;
            faultBox.style.alignItems = Align.FlexStart;
            faultBox.style.paddingLeft = 10;
            faultBox.style.paddingRight = 10;
            faultBox.style.paddingTop = 5;
            faultBox.style.paddingBottom = 6;
            faultBox.style.backgroundColor = Theme.Alpha(Theme.Red, 0.18f);
            faultBox.style.borderTopWidth = 1;
            faultBox.style.borderTopColor = Theme.Red;
            var bang = Theme.Tag("err", Theme.Red, 9);
            bang.style.marginRight = 6;
            bang.style.marginTop = 1;
            bang.style.flexShrink = 0;
            faultBox.Add(bang);
            faultText = new Label { pickingMode = PickingMode.Ignore };
            faultText.style.whiteSpace = WhiteSpace.Normal;
            faultText.style.fontSize = 11;
            faultText.style.color = Theme.Alpha(Color.Lerp(Theme.Red, Color.white, 0.35f), 1f);
            faultText.style.flexShrink = 1;
            faultBox.Add(faultText);
            Add(faultBox);

            // 警告テープ：ノードの上に浮かべる（見出しの位置は変えない。つなぐ丸の位置がずれないように）
            tape = new VisualElement { name = "fault-tape", pickingMode = PickingMode.Ignore };
            tape.style.position = Position.Absolute;
            tape.style.left = 0;
            tape.style.right = 0;
            tape.style.top = -11;
            tape.style.height = 7;
            tape.style.overflow = Overflow.Hidden;
            tape.style.display = DisplayStyle.None;
            tape.style.backgroundColor = new Color(0.05f, 0.03f, 0.02f, 0.95f);
            tapeStripes = new VisualElement { pickingMode = PickingMode.Ignore };
            tapeStripes.style.position = Position.Absolute;
            tapeStripes.style.left = tapeStripes.style.top = 0;
            tapeStripes.style.right = tapeStripes.style.bottom = 0;
            tapeStripes.generateVisualContent += DrawTape;
            tape.Add(tapeStripes);
            Add(tape);

            InPort = MakePort(left: true);
            OutPort = MakePort(left: false);
            if (Node.HasInput(node.Kind)) Add(InPort);
            if (Node.HasOutput(node.Kind)) Add(OutPort);
            brackets = Theme.BracketsOverlay(() => problem ? Theme.Alpha(Theme.Red, 0.5f + 0.5f * pulse)
                : selected ? Theme.Alpha(Theme.Amber, 0.45f + 0.55f * pulse) : Theme.Alpha(kc, 0.9f), 10, 2f);
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

        /// <summary>
        /// 明滅を進める（t：秒）。選んでいるノードは 1.6 秒で1周。問題のあるノードは 0.7 秒で1周と速く強く、警告テープの縞が流れる
        /// </summary>
        public void Pulse(float t)
        {
            pulse = 0.5f + 0.5f * Mathf.Sin(t * Mathf.PI * 2 / (problem ? 0.7f : 1.6f));
            glow.MarkDirtyRepaint();
            brackets.MarkDirtyRepaint();
            if (problem)
            {
                tapePhase = Mathf.Repeat(t * 22f, 14f);
                tapeStripes.MarkDirtyRepaint();
                faultChip.style.opacity = 0.55f + 0.45f * pulse;
            }
        }

        /// <summary>警告テープの斜めの縞（アンバーと黒。右へ流れる）</summary>
        void DrawTape(MeshGenerationContext ctx)
        {
            var w = tapeStripes.layout.width;
            var h = tapeStripes.layout.height;
            if (float.IsNaN(w) || float.IsNaN(h)) return;
            var p = ctx.painter2D;
            p.fillColor = Theme.Amber;
            const float step = 14f, band = 7f;
            for (float x = -step * 2 + tapePhase; x < w + step; x += step)
            {
                p.BeginPath();
                p.MoveTo(new Vector2(x, h));
                p.LineTo(new Vector2(x + h, 0));
                p.LineTo(new Vector2(x + h + band, 0));
                p.LineTo(new Vector2(x + band, h));
                p.ClosePath();
                p.Fill();
            }
        }

        /// <summary>ノードの外側に、だんだん薄くなる線を重ねて光彩にする（ノードの内側には描かない）</summary>
        void DrawGlow(MeshGenerationContext ctx)
        {
            if (!selected && !problem) return;
            // 問題のあるノードは赤で、選んでいるときより強く明滅する
            var c = problem ? Theme.Red : Theme.Amber;
            float strength = problem ? 0.16f + 0.34f * pulse : 0.12f + 0.2f * pulse;
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
            style.backgroundColor = problem ? Color.Lerp(Theme.Panel, Theme.Red, 0.12f) : Theme.Panel;
            Theme.Border(style, problem ? 2 : 1, problem ? Theme.Red : selected ? Theme.Amber : Theme.Line);
            brackets?.MarkDirtyRepaint();
            glow?.MarkDirtyRepaint();
        }

        public void SetSelected(bool on) { selected = on; pulse = 1; Paint(); }

        /// <summary>問題があるか（why：問題の文。ノードの下に出す）</summary>
        public void SetProblem(bool on, string why = null)
        {
            problem = on;
            pulse = 1;
            var show = on ? DisplayStyle.Flex : DisplayStyle.None;
            tape.style.display = show;
            faultChip.style.display = show;
            faultBox.style.display = on && !string.IsNullOrEmpty(why) ? DisplayStyle.Flex : DisplayStyle.None;
            faultText.text = why ?? "";
            idTag.style.display = on ? DisplayStyle.None : DisplayStyle.Flex;
            Paint();
        }

        /// <summary>問題の文（出していなければ空。自動テスト用）</summary>
        public string FaultText => problem ? faultText.text : "";

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
                (n.Rules.HandLimit > 0 ? $"\n手札の上限 {n.Rules.HandLimit}枚" : "") +
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
