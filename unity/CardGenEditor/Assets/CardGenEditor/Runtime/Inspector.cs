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

        /// <summary>「列,行」を空白か「、」で区切って並べたもの（例：22,25 23,25）</summary>
        public static string CellsText(IEnumerable<Cell> cells) => string.Join(" ", cells.Select(c => $"{c.Col},{c.Row}"));

        /// <summary>CellsText を読む。読めない書き方があれば null</summary>
        public static List<Cell> ParseCells(string s)
        {
            var result = new List<Cell>();
            foreach (var tok in s.Split(new[] { ' ', '　', '、', '/', '／', ';' }, StringSplitOptions.RemoveEmptyEntries))
            {
                var xy = tok.Replace('，', ',').Trim('(', ')', '（', '）').Split(',');
                if (xy.Length != 2 || !int.TryParse(xy[0], out var c) || !int.TryParse(xy[1], out var r) || c < 0 || r < 0) return null;
                result.Add(new Cell(c, r));
            }
            return result;
        }

        /// <summary>置ける枚数の上限を「種類+種類=枚数」をスペースで区切った文字列にする（例：「土地=1 魔法+罠=2」）</summary>
        public static string LimitsText(IEnumerable<PlaceLimit> ls) =>
            string.Join(" ", ls.Select(l => $"{string.Join("+", l.Types)}={l.Count}"));

        /// <summary>LimitsText を読む。読めない書き方があれば null</summary>
        public static List<PlaceLimit> ParseLimits(string s)
        {
            var result = new List<PlaceLimit>();
            foreach (var tok in s.Split(new[] { ' ', '　', '、', ',', ';' }, StringSplitOptions.RemoveEmptyEntries))
            {
                var kv = tok.Replace('＝', '=').Split('=');
                if (kv.Length != 2 || !int.TryParse(kv[1], out var n) || n < 0) return null;
                var types = kv[0].Split(new[] { '+', '＋' }, StringSplitOptions.RemoveEmptyEntries).Select(t => t.Trim()).ToList();
                result.Add(new PlaceLimit { Types = types, Count = n });
            }
            return result;
        }

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

        void SignedInt(string label, int value, Action<int> set)
        {
            var f = new IntegerField(label) { value = value, isDelayed = true };
            f.RegisterValueChangedCallback(e => { set(e.newValue); Changed(); });
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
                    Int("初期ライフ", n.Rules.Life, v => n.Rules.Life = v);
                    ListField("戦闘できる種類", n.Rules.Fighters, v => n.Rules.Fighters = v);
                    Hint("戦闘できる種類のカードは、表側表示で相手の戦闘できるカードを攻撃できます（相手にいなければ直接攻撃）。");
                    Int("1ターンの召喚の上限", n.Rules.SummonsPerTurn, v => n.Rules.SummonsPerTurn = v);
                    Int("ターンの最初に引く枚数", n.Rules.DrawPerTurn, v => n.Rules.DrawPerTurn = v);
                    Toggle("先攻の最初のターンも引く", n.Rules.FirstTurnDraw, v => n.Rules.FirstTurnDraw = v);
                    Toggle("先攻の最初のターンも攻撃できる", n.Rules.FirstTurnAttack, v => n.Rules.FirstTurnAttack = v);
                    Hint("召喚の上限は、戦闘できる種類のカードを1ターンに置ける枚数です（0 なら制限なし）。攻撃は1ターンに1枚1回です。");
                    var limits = new TextField("種類ごとの上限") { value = LimitsText(n.Rules.PlaceLimits), isDelayed = true };
                    limits.RegisterValueChangedCallback(e =>
                    {
                        var parsed = ParseLimits(e.newValue);
                        if (parsed == null) { limits.SetValueWithoutNotify(LimitsText(n.Rules.PlaceLimits)); return; }
                        n.Rules.PlaceLimits = parsed;
                        Changed();
                    });
                    Add(limits);
                    Hint("1ターンに置ける枚数の上限を、種類ごとに「種類=枚数」で書きます（例：「土地=1」。種類をまとめるなら「魔法+罠=2」）。");
                    Toggle("攻撃するとタップする", n.Rules.AttackTaps, v => n.Rules.AttackTaps = v);
                    Toggle("召喚酔い（置いたターンは攻撃・タップできない）", n.Rules.SummoningSickness, v => n.Rules.SummoningSickness = v);
                    Hint("マナ：ターンプレイヤーは、マナを出すカードをタップしてマナを得て、カードのコストを支払って置きます。" +
                         "マナはターンの終わりに消え、タップしたカードは持ち主の次のターンの始めに起きます。");
                    break;
                case NodeKind.Zone:
                    Hint("1人分のゾーン。相手のフィールドは同じ形になります（共通ルール②）。");
                    Text("名前", n.Zone.Name, v => n.Zone.Name = v);
                    Int("マスの数", n.Zone.Count, v => n.Zone.Count = v);
                    Choice("容量", new[] { ("1枚まで", Capacity.One), ("何枚でも", Capacity.Many) }, n.Zone.Capacity, v => n.Zone.Capacity = v);
                    Choice("役割", new[] { ("その他", ZoneRole.Plain), ("デッキ", ZoneRole.Deck), ("墓地", ZoneRole.Grave) }, n.Zone.Role, v => n.Zone.Role = v);
                    Toggle("フィールド上に数える", n.Zone.OnField, v => n.Zone.OnField = v);
                    ListField("置ける種類", n.Zone.Admits, v => n.Zone.Admits = v);
                    var cells = new TextField("マスの位置") { value = CellsText(n.Zone.Cells), isDelayed = true };
                    cells.RegisterValueChangedCallback(e =>
                    {
                        var parsed = ParseCells(e.newValue);
                        if (parsed == null) { cells.SetValueWithoutNotify(CellsText(n.Zone.Cells)); return; }
                        n.Zone.Cells = parsed;
                        Changed();
                    });
                    Add(cells);
                    var row = new VisualElement();
                    row.style.flexDirection = FlexDirection.Row;
                    var lineCol = new IntegerField("左端の列") { value = n.Zone.Cells.Count > 0 ? n.Zone.Cells[0].Col : 22 };
                    var lineRow = new IntegerField("行") { value = n.Zone.Cells.Count > 0 ? n.Zone.Cells[0].Row : 25 };
                    lineCol.style.flexGrow = 1;
                    lineRow.style.flexGrow = 1;
                    row.Add(lineCol);
                    row.Add(lineRow);
                    Add(row);
                    var line = new Button(() =>
                    {
                        n.Zone.Cells = Enumerable.Range(0, n.Zone.Count).Select(i => new Cell(lineCol.value + i, lineRow.value)).ToList();
                        Changed();
                        Show(n);
                    }) { text = "マスの数だけ横に並べる" };
                    Add(line);
                    var clear = new Button(() => { n.Zone.Cells = new List<Cell>(); Changed(); Show(n); }) { text = "マス目の上に置かない" };
                    Add(clear);
                    Hint($"盤面全体（2人分）は {Grid.Size}×{Grid.Size} のマス目です。マスの位置は「列,行」をマスの数だけ並べます（自分の側。" +
                         $"相手の側は中心のマス（{Grid.Size / 2}, {Grid.Size / 2}）について点対称の位置）。空なら、マス目の上にないゾーンです" +
                         "（「隣」「同じ縦列」の範囲に入りません）。遊戯王の見本は、モンスターが行 25、魔法・罠が行 26、列 22〜26 です。");
                    break;
                case NodeKind.Card:
                    Hint("カード。効果のノード（発動・無効・攻撃力の変化）をつなぎます。");
                    Text("名前", n.Card.Name, v => n.Card.Name = v);
                    Text("種類", n.Card.Type, v => n.Card.Type = v.Trim());
                    ListField("タグ", n.Card.Tags, v => n.Card.Tags = v);
                    Int("攻撃力", n.Card.Attack, v => n.Card.Attack = v);
                    Int("守備力", n.Card.Defense, v => n.Card.Defense = v);
                    Int("コスト（置くのに払うマナ）", n.Card.Cost, v => n.Card.Cost = Math.Max(0, v));
                    Int("タップで出るマナ", n.Card.Mana, v => n.Card.Mana = Math.Max(0, v));
                    break;
                case NodeKind.Activate:
                    Hint("発動し、解決したときに、つないだ動き（破壊・手札に戻す・ドロー・ダメージ・回復）を上から順に行います。無効にされていれば何も起きません。");
                    break;
                case NodeKind.Destroy:
                    Hint("つないだ範囲のカードをすべて破壊し、持ち主の墓地へ送ります。範囲のノードを1つつなぎます。");
                    break;
                case NodeKind.Bounce:
                    Hint("つないだ範囲のカードをすべて持ち主の手札に戻します。範囲のノードを1つつなぎます。");
                    break;
                case NodeKind.Draw:
                    Hint("発動したプレイヤーがデッキからカードを引きます（足りなければある分だけ）。");
                    Int("枚数", n.DrawCount, v => n.DrawCount = Math.Max(1, v));
                    break;
                case NodeKind.Negate:
                    Hint("このカードが表側表示でフィールド上に存在する限り、つないだ範囲のカードの効果を無効にします。範囲のノードを1つつなぎます。");
                    break;
                case NodeKind.Boost:
                    Hint("このカードが表側表示でフィールド上に存在し、効果が無効にされていない限り、つないだ範囲のカードの攻撃力を変えます（負の数なら下げる。0 未満にはならない）。範囲のノードを1つつなぎます。");
                    SignedInt("変える量", n.Amount, v => n.Amount = v);
                    break;
                case NodeKind.Damage:
                    Hint("相手のライフを減らします（0 より下がらない）。");
                    Int("ダメージ", n.Amount, v => n.Amount = Math.Max(1, v));
                    break;
                case NodeKind.Heal:
                    Hint("発動したプレイヤーのライフを増やします。");
                    Int("回復する量", n.Amount, v => n.Amount = Math.Max(1, v));
                    break;
                case NodeKind.Selector:
                    Hint("フィールド上のカードのうち、すべての条件に合うものを選びます。");
                    ListField("カードの種類", n.Selector.Types, v => n.Selector.Types = v);
                    ListField("タグ（すべて持つ）", n.Selector.Tags, v => n.Selector.Tags = v);
                    Choice("陣営", new[] { ("お互い", Side.Both), ("自分", Side.Self), ("相手", Side.Opp) }, n.Selector.Side, v => n.Selector.Side = v);
                    Toggle("表側表示のカードだけ", n.Selector.FaceUpOnly, v => n.Selector.FaceUpOnly = v);
                    Toggle("このカード自身を除く", n.Selector.ExcludeSelf, v => n.Selector.ExcludeSelf = v);
                    Choice("マスの関係", new[] { ("条件なし", Near.Any), ("隣のマス", Near.Adjacent), ("同じ縦列", Near.SameColumn) },
                        n.Selector.Near, v => n.Selector.Near = v);
                    Hint("マスの関係は、効果を持つカードのマスから見ます（発動した魔法・罠は、置かれていたマス）。「隣」は上下左右、" +
                         "「同じ縦列」は相手の側も含みます。マス目の上にないカードは入りません。無効の範囲にはまだ使えません。");
                    break;
            }
        }
    }
}
