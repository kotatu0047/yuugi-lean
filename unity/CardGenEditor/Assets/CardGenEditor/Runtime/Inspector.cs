using System;
using System.Collections.Generic;
using System.Linq;
using UnityEngine;
using UnityEngine.UIElements;

namespace CardGen.App
{
    /// <summary>選んだノードの中身を編集するパネル</summary>
    public sealed class Inspector : VisualElement
    {
        public event Action<Node> Edited;
        Node node;

        public Inspector()
        {
            style.paddingLeft = 12;
            style.paddingRight = 12;
            style.paddingTop = 10;
            style.paddingBottom = 10;
            Show(null);
        }

        static List<string> SplitList(string s) =>
            s.Split(new[] { ',', '、', '・', '，' }, StringSplitOptions.RemoveEmptyEntries)
             .Select(x => x.Trim()).Where(x => x.Length > 0).ToList();

        static string JoinList(IEnumerable<string> l) => string.Join("、", l);

        void Changed() => Edited?.Invoke(node);

        void Heading(string text)
        {
            var l = new Label(text);
            l.style.unityFontStyleAndWeight = FontStyle.Bold;
            l.style.fontSize = 15;
            l.style.marginBottom = 8;
            l.style.color = Color.white;
            Add(l);
        }

        void Hint(string text)
        {
            var l = new Label(text);
            l.style.whiteSpace = WhiteSpace.Normal;
            l.style.fontSize = 11;
            l.style.color = new Color(0.7f, 0.7f, 0.75f);
            l.style.marginBottom = 6;
            Add(l);
        }

        void Text(string label, string value, Action<string> set)
        {
            var f = new TextField(label) { value = value, isDelayed = true };
            f.RegisterValueChangedCallback(e => { set(e.newValue); Changed(); });
            Add(f);
        }

        void ListField(string label, List<string> value, Action<List<string>> set) =>
            Text(label, JoinList(value), v => set(SplitList(v)));

        void Int(string label, int value, Action<int> set)
        {
            var f = new IntegerField(label) { value = value, isDelayed = true };
            f.RegisterValueChangedCallback(e => { set(Math.Max(0, e.newValue)); Changed(); });
            Add(f);
        }

        void Toggle(string label, bool value, Action<bool> set)
        {
            var f = new Toggle(label) { value = value };
            f.RegisterValueChangedCallback(e => { set(e.newValue); Changed(); });
            Add(f);
        }

        void Choice<T>(string label, (string, T)[] choices, T value, Action<T> set)
        {
            var labels = choices.Select(c => c.Item1).ToList();
            var idx = Math.Max(0, Array.FindIndex(choices, c => EqualityComparer<T>.Default.Equals(c.Item2, value)));
            var f = new DropdownField(label, labels, idx);
            f.RegisterValueChangedCallback(e => { set(choices[labels.IndexOf(e.newValue)].Item2); Changed(); });
            Add(f);
        }

        public void Show(Node n)
        {
            node = n;
            Clear();
            if (n == null)
            {
                Heading("ノード");
                Hint("ノードを選ぶと、ここで中身を編集できます。\n" +
                     "・背景をドラッグ：移動　・ホイール：拡大縮小\n" +
                     "・右の丸から左の丸へドラッグ：つなぐ　・左の丸をクリック：つなぎを外す\n" +
                     "・ノードを選んだまま「追加」：そのノードからつないだ状態で追加");
                return;
            }
            Heading(Node.KindLabel(n.Kind));
            switch (n.Kind)
            {
                case NodeKind.Rules:
                    Hint("ゲーム全体のルール。ゾーンのノードをつなぐと、上から順にゾーンになります。");
                    ListField("カードの種類", n.Rules.CardTypes, v => n.Rules.CardTypes = v);
                    Int("デッキの枚数", n.Rules.DeckSize, v => n.Rules.DeckSize = v);
                    Int("初期手札", n.Rules.HandSize, v => n.Rules.HandSize = v);
                    break;
                case NodeKind.Zone:
                    Hint("1人分のゾーン。相手のフィールドは同じ形になります（共通ルール②）。");
                    Text("名前", n.Zone.Name, v => n.Zone.Name = v);
                    Int("マスの数", n.Zone.Count, v => n.Zone.Count = v);
                    Choice("容量", new[] { ("1枚まで", Capacity.One), ("何枚でも", Capacity.Many) }, n.Zone.Capacity, v => n.Zone.Capacity = v);
                    Choice("役割", new[] { ("その他", ZoneRole.Plain), ("デッキ", ZoneRole.Deck), ("墓地", ZoneRole.Grave) }, n.Zone.Role, v => n.Zone.Role = v);
                    Toggle("フィールド上に数える", n.Zone.OnField, v => n.Zone.OnField = v);
                    ListField("置ける種類", n.Zone.Admits, v => n.Zone.Admits = v);
                    break;
                case NodeKind.Card:
                    Hint("カード。効果のノード（発動して破壊・無効）をつなぎます。");
                    Text("名前", n.Card.Name, v => n.Card.Name = v);
                    Text("種類", n.Card.Type, v => n.Card.Type = v.Trim());
                    ListField("タグ", n.Card.Tags, v => n.Card.Tags = v);
                    break;
                case NodeKind.Destroy:
                    Hint("発動し、解決したときに、つないだ範囲のカードを上から順にすべて破壊して持ち主の墓地へ送ります。範囲のノードをつなぎます。");
                    break;
                case NodeKind.Negate:
                    Hint("このカードが表側表示でフィールド上に存在する限り、つないだ範囲のカードの効果を無効にします。範囲のノードを1つつなぎます。");
                    break;
                case NodeKind.Selector:
                    Hint("フィールド上のカードのうち、すべての条件に合うものを選びます。");
                    ListField("カードの種類", n.Selector.Types, v => n.Selector.Types = v);
                    ListField("タグ（すべて持つ）", n.Selector.Tags, v => n.Selector.Tags = v);
                    Choice("陣営", new[] { ("お互い", Side.Both), ("自分", Side.Self), ("相手", Side.Opp) }, n.Selector.Side, v => n.Selector.Side = v);
                    Toggle("表側表示のカードだけ", n.Selector.FaceUpOnly, v => n.Selector.FaceUpOnly = v);
                    Toggle("このカード自身を除く", n.Selector.ExcludeSelf, v => n.Selector.ExcludeSelf = v);
                    break;
            }
        }
    }
}
