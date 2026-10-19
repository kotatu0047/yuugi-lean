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

        /// <summary>集合のノードの中身（カードの種類・マナの色・タグの集合）。選ぶ形の入力に使う</summary>
        public Func<SetsData> Sets = () => null;

        /// <summary>集合の値の名前を変える（使っているところもすべて書き換える）</summary>
        public Action<SetKind, string, string> Rename = (k, a, b) => { };

        // 名前を変えようとしている集合の値（集合のリストと値）
        List<string> renameList;
        string renameValue;

        static readonly Color ChipOn = new Color(0.28f, 0.45f, 0.62f);
        static readonly Color ChipOff = new Color(0.22f, 0.22f, 0.25f);
        static readonly Color ChipBad = new Color(0.55f, 0.22f, 0.22f);

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

        static VisualElement Wrap()
        {
            var r = new VisualElement();
            r.style.flexDirection = FlexDirection.Row;
            r.style.flexWrap = UnityEngine.UIElements.Wrap.Wrap;
            r.style.alignItems = Align.Center;
            return r;
        }

        static Button Chip(string text, Color bg, System.Action click)
        {
            var b = new Button(click) { text = text };
            b.style.backgroundColor = bg;
            b.style.marginLeft = 0;
            b.style.marginRight = 4;
            b.style.marginTop = 2;
            b.style.marginBottom = 2;
            b.style.paddingLeft = 8;
            b.style.paddingRight = 8;
            b.style.borderTopLeftRadius = b.style.borderTopRightRadius = b.style.borderBottomLeftRadius = b.style.borderBottomRightRadius = 10;
            return b;
        }

        Label FieldLabel(string text)
        {
            var l = new Label(text);
            l.style.marginTop = 6;
            l.style.marginBottom = 2;
            l.style.color = new Color(0.82f, 0.82f, 0.86f);
            return l;
        }

        /// <summary>
        /// 集合から選ぶ（いくつでも）。選んでいる値は色つき。集合にない値が選ばれていれば赤で出し、押すと外す
        /// </summary>
        void Picker(string label, IReadOnlyList<string> options, List<string> selected, string empty = "（集合のノードで値を加えてください）")
        {
            Add(FieldLabel(label));
            var row = Wrap();
            foreach (var o in options)
            {
                var on = selected.Contains(o);
                var v = o;
                row.Add(Chip(o, on ? ChipOn : ChipOff, () =>
                {
                    if (selected.Contains(v)) selected.Remove(v); else selected.Add(v);
                    Changed();
                    Show(node);
                }));
            }
            foreach (var bad in selected.Where(x => !options.Contains(x)).Distinct().ToList())
                row.Add(Chip($"{bad}（集合にない）×", ChipBad, () => { selected.RemoveAll(x => x == bad); Changed(); Show(node); }));
            if (row.childCount == 0) row.Add(new Label(empty) { style = { color = new Color(0.6f, 0.6f, 0.65f), fontSize = 11 } });
            Add(row);
        }

        /// <summary>集合から1つ選ぶ</summary>
        void Pick(string label, IReadOnlyList<string> options, string value, Action<string> set, string noneLabel = null)
        {
            var labels = new List<string>();
            var values = new List<string>();
            if (noneLabel != null) { labels.Add(noneLabel); values.Add(""); }
            foreach (var o in options) { labels.Add(o); values.Add(o); }
            if (!values.Contains(value)) { labels.Add($"{value}（集合にない）"); values.Add(value); }
            var f = new DropdownField(label, labels, values.IndexOf(value));
            f.RegisterValueChangedCallback(e => { set(values[labels.IndexOf(e.newValue)]); Changed(); });
            Add(f);
        }

        /// <summary>タグ：タグの集合ごとに選ぶ。タグの集合がなければ自由に書く</summary>
        void TagPicker(string label, List<string> tags, Action<List<string>> set)
        {
            var sets = Sets();
            if (sets == null || sets.TagSets.Count == 0)
            {
                ListField(label, tags, set);
                Hint("集合のノードでタグの集合（例：属性、種族）を作ると、ここで選べるようになります。");
                return;
            }
            Add(FieldLabel(label));
            foreach (var ts in sets.TagSets)
            {
                var row = Wrap();
                // 集合の名前は1行に置き、値はその下に並べる（長い名前でも切れないように）
                var name = new Label(ts.Name);
                name.style.width = Length.Percent(100);
                name.style.fontSize = 11;
                name.style.color = new Color(0.65f, 0.65f, 0.7f);
                row.Add(name);
                foreach (var o in ts.Values)
                {
                    var v = o;
                    row.Add(Chip(o, tags.Contains(o) ? ChipOn : ChipOff, () =>
                    {
                        if (tags.Contains(v)) tags.Remove(v); else tags.Add(v);
                        Changed();
                        Show(node);
                    }));
                }
                Add(row);
            }
            var all = sets.TagSets.SelectMany(t => t.Values).ToList();
            var bad = tags.Where(x => !all.Contains(x)).Distinct().ToList();
            if (bad.Count > 0)
            {
                var row = Wrap();
                foreach (var b in bad)
                    row.Add(Chip($"{b}（集合にない）×", ChipBad, () => { tags.RemoveAll(x => x == b); Changed(); Show(node); }));
                Add(row);
            }
        }

        /// <summary>集合1つの編集：値のチップ（×で消す）と、加える欄</summary>
        void SetEditor(SetKind kind, string title, List<string> values, string placeholder, System.Action remove = null,
            TextField nameField = null)
        {
            var box = new VisualElement();
            box.style.marginTop = 8;
            box.style.paddingLeft = 8;
            box.style.paddingRight = 8;
            box.style.paddingTop = 6;
            box.style.paddingBottom = 6;
            box.style.backgroundColor = new Color(0.14f, 0.15f, 0.17f);
            box.style.borderTopLeftRadius = box.style.borderTopRightRadius = box.style.borderBottomLeftRadius = box.style.borderBottomRightRadius = 6;
            var head = Wrap();
            if (nameField != null) { nameField.style.flexGrow = 1; head.Add(nameField); }
            else head.Add(new Label(title) { style = { unityFontStyleAndWeight = FontStyle.Bold, color = Color.white, flexGrow = 1 } });
            if (remove != null) head.Add(new Button(remove) { text = "集合を削除" });
            box.Add(head);
            var chips = Wrap();
            foreach (var v in values)
            {
                var x = v;
                // 値を押すと名前を変える欄が出る。× で消す
                var editing = renameList == values && renameValue == x;
                chips.Add(Chip(v, editing ? new Color(0.55f, 0.45f, 0.2f) : ChipOn, () =>
                {
                    (renameList, renameValue) = editing ? (null, null) : (values, x);
                    Show(node);
                }));
                var del = Chip("×", ChipOff, () => { values.Remove(x); Changed(); Show(node); });
                del.style.marginLeft = -4;
                del.style.marginRight = 8;
                chips.Add(del);
            }
            if (values.Count == 0) chips.Add(new Label("（まだありません）") { style = { color = new Color(0.6f, 0.6f, 0.65f), fontSize = 11 } });
            box.Add(chips);
            if (renameList == values && values.Contains(renameValue))
            {
                var rrow = Wrap();
                rrow.style.flexWrap = UnityEngine.UIElements.Wrap.NoWrap;
                var to = new TextField($"「{renameValue}」の新しい名前") { value = renameValue };
                to.style.flexGrow = 1;
                void Apply()
                {
                    var nv = to.value.Trim();
                    if (nv.Length == 0 || nv == renameValue || values.Contains(nv)) return;
                    Rename(kind, renameValue, nv);
                    (renameList, renameValue) = (null, null);
                    Changed();
                    Show(node);
                }
                to.RegisterCallback<KeyDownEvent>(e => { if (e.keyCode == KeyCode.Return || e.keyCode == KeyCode.KeypadEnter) Apply(); });
                rrow.Add(to);
                rrow.Add(new Button(Apply) { text = "名前を変える" });
                box.Add(rrow);
                box.Add(new Label("使っているカード・ゾーン・ルール・範囲も、まとめて新しい名前に変わります") { style = { fontSize = 10, color = new Color(0.8f, 0.7f, 0.4f) } });
            }
            var addRow = Wrap();
            addRow.style.flexWrap = UnityEngine.UIElements.Wrap.NoWrap;
            var input = new TextField { value = "" };
            input.style.flexGrow = 1;
            input.tooltip = placeholder;
            void AddValue()
            {
                var added = false;
                foreach (var v in SplitList(input.value))
                    if (!values.Contains(v)) { values.Add(v); added = true; }
                if (!added) return;
                Changed();
                Show(node);
            }
            input.RegisterCallback<KeyDownEvent>(e => { if (e.keyCode == KeyCode.Return || e.keyCode == KeyCode.KeypadEnter) AddValue(); });
            addRow.Add(input);
            addRow.Add(new Button(AddValue) { text = "加える" });
            box.Add(addRow);
            box.Add(new Label(placeholder) { style = { fontSize = 10, color = new Color(0.55f, 0.55f, 0.6f) } });
            Add(box);
        }

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
            var sets = Sets() ?? new SetsData();
            switch (n.Kind)
            {
                case NodeKind.Axioms:
                    Hint("すべてのゲームに共通の前提です。編集・削除はできません（Lean のモデルと C# のエンジンがこれを前提にしています）。");
                    for (int i = 0; i < Axioms.Lines.Length; i++)
                    {
                        var l = new Label($"{i + 1}. {Axioms.Lines[i]}");
                        l.style.whiteSpace = WhiteSpace.Normal;
                        l.style.marginBottom = 4;
                        l.style.color = new Color(0.88f, 0.88f, 0.9f);
                        Add(l);
                    }
                    break;
                case NodeKind.Sets:
                    Hint("ゲームで使う値の集合です。ルール・ゾーン・カード・範囲の種類やタグ、マナの色は、ここから選びます。");
                    Hint("値を押すと名前を変えられます（使っているところもまとめて変わります）。× で消します。");
                    SetEditor(SetKind.CardType, "カードの種類", n.Sets.CardTypes, "例：モンスター、魔法、罠（「、」で区切ると、まとめて加えられます）");
                    SetEditor(SetKind.ManaColor, "マナの色", n.Sets.ManaColors, "例：白、青、黒、赤、緑（色のマナを使わなければ空）");
                    Add(FieldLabel("タグの集合（属性・種族など）"));
                    Hint("タグの集合を1つでも作ると、カードと範囲のタグは、どれかの集合の値から選びます（集合にないタグは形式の誤り）。");
                    foreach (var ts in n.Sets.TagSets.ToList())
                    {
                        var t = ts;
                        var nameField = new TextField { value = t.Name, isDelayed = true };
                        nameField.RegisterValueChangedCallback(e => { t.Name = e.newValue.Trim(); Changed(); });
                        SetEditor(SetKind.Tag, t.Name, t.Values, "値を加える（例：闇属性、光属性）",
                            remove: () => { n.Sets.TagSets.Remove(t); Changed(); Show(n); }, nameField: nameField);
                    }
                    var newSet = new Button(() =>
                    {
                        var k = 1;
                        while (n.Sets.TagSets.Any(x => x.Name == $"タグの集合{k}")) k++;
                        n.Sets.TagSets.Add(new TagSet { Name = $"タグの集合{k}" });
                        Changed();
                        Show(n);
                    }) { text = "タグの集合を加える" };
                    newSet.style.marginTop = 8;
                    Add(newSet);
                    break;
                case NodeKind.Rules:
                    Hint("ゲーム全体のルール。ゾーンのノードをつなぐと、上から順にゾーンになります。カードの種類とマナの色は、上の集合のノードで決めます。");
                    Int("デッキの枚数", n.Rules.DeckSize, v => n.Rules.DeckSize = v);
                    Int("初期手札", n.Rules.HandSize, v => n.Rules.HandSize = v);
                    Int("初期ライフ", n.Rules.Life, v => n.Rules.Life = v);
                    Picker("戦闘できる種類", sets.CardTypes, n.Rules.Fighters);
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
                    Toggle("MTG 式の戦闘（守る側がブロックを選ぶ）", n.Rules.Blocking, v => n.Rules.Blocking = v);
                    Hint("MTG 式の戦闘：攻撃するカードを宣言し（何枚でも）、攻撃されたプレイヤーがブロックするカードを選びます" +
                         "（1枚の攻撃を何枚でブロックしてもよい。選ばなければ攻撃力のダメージ）。ブロックされたら、攻撃力（パワー）と" +
                         "守備力（タフネス）で互いにダメージを与え、守備力以上のダメージを受けたカードを破壊します。ダメージはターンの終わりまで残ります。");
                    Picker("いつでも置ける種類（インスタント）", sets.CardTypes, n.Rules.Instants);
                    Toggle("スタック（呪文は後に置いたものから解決）", n.Rules.Stack, v => n.Rules.Stack = v);
                    Hint("インスタントは、相手のターンや、攻撃・スタックへの応答としても置けます（相手のターンには、自分のカードをタップして払う）。" +
                         "スタック：「フィールド上」でないゾーンに置いた、発動する効果を持つカードは、後に置いたものから解決します。" +
                         "スタックが空でなければ、インスタント以外は置けず、攻撃・ブロック・ターン終了もできません。");
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
                    Picker("置ける種類", sets.CardTypes, n.Zone.Admits);
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
                    Hint("カード。効果のノード（発動・無効・攻撃力の変化・守備力の変化）をつなぎます。");
                    Text("名前", n.Card.Name, v => n.Card.Name = v);
                    Pick("種類", sets.CardTypes, n.Card.Type, v => n.Card.Type = v);
                    TagPicker("タグ", n.Card.Tags, v => n.Card.Tags = v);
                    Int("攻撃力", n.Card.Attack, v => n.Card.Attack = v);
                    Int("守備力", n.Card.Defense, v => n.Card.Defense = v);
                    Toggle("トランプル（MTG 式の戦闘で、余ったダメージを相手に）", n.Card.Trample, v => n.Card.Trample = v);
                    Toggle("飛行（飛行か到達を持つカードでしかブロックできない）", n.Card.Flying, v => n.Card.Flying = v);
                    Toggle("到達（飛行を持つカードもブロックできる）", n.Card.Reach, v => n.Card.Reach = v);
                    Int("コスト（どの色でも払える分）", n.Card.Cost, v => n.Card.Cost = Math.Max(0, v));
                    if (sets.ManaColors.Count > 0)
                    {
                        Add(FieldLabel("コスト（色の決まった分）"));
                        var colorRow = Wrap();
                        foreach (var col in sets.ManaColors.Concat(n.Card.ColorCost.Where(x => !sets.ManaColors.Contains(x)).Distinct()).ToList())
                        {
                            var c = col;
                            var f = new IntegerField(c) { value = n.Card.ColorCost.Count(x => x == c), isDelayed = true };
                            f.labelElement.style.minWidth = 0;
                            f.labelElement.style.width = 40;
                            f.style.width = 90;
                            f.RegisterValueChangedCallback(e =>
                            {
                                // 色の順番は集合の順に揃える
                                var counts = (sets.ManaColors.Contains(c) ? sets.ManaColors : sets.ManaColors.Append(c).ToList())
                                    .ToDictionary(x => x, x => x == c ? Math.Max(0, e.newValue) : n.Card.ColorCost.Count(y => y == x));
                                n.Card.ColorCost = counts.SelectMany(kv => Enumerable.Repeat(kv.Key, kv.Value)).ToList();
                                Changed();
                            });
                            colorRow.Add(f);
                        }
                        Add(colorRow);
                    }
                    Int("タップで出るマナの量", n.Card.Mana, v => n.Card.Mana = Math.Max(0, v));
                    Pick("タップで出るマナの色", sets.ManaColors, n.Card.ManaColor, v => n.Card.ManaColor = v, noneLabel: "無色");
                    if (sets.ManaColors.Count > 0)
                        Picker("選べるマナの色（2色以上の土地）", sets.ManaColors, n.Card.ManaChoice);
                    Hint("マナの色は、集合のノードの「マナの色」から選びます。「選べるマナの色」を選ぶと、タップするたびにその中から1色を選んで出します" +
                         "（そのときは「タップで出るマナの色」は無色にします）。");
                    break;
                case NodeKind.Activate:
                    Hint("発動し、解決したときに、つないだ動き（破壊・手札に戻す・ドロー・ダメージ・回復・カードへのダメージ）を上から順に行います。無効にされていれば何も起きません。");
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
                case NodeKind.Toughen:
                    Hint("このカードが表側表示でフィールド上に存在し、効果が無効にされていない限り、つないだ範囲のカードの守備力を変えます（負の数なら下げる。0 未満にはならない）。範囲のノードを1つつなぎます。");
                    SignedInt("変える量", n.Amount, v => n.Amount = v);
                    break;
                case NodeKind.Strike:
                    Hint("つないだ範囲の、戦闘できるカードすべてにダメージを与えます。ダメージはターンの終わりまで残り、守備力以上のダメージを受けたカードは破壊されます。範囲のノードを1つつなぎます。");
                    Int("ダメージ", n.Amount, v => n.Amount = Math.Max(1, v));
                    break;
                case NodeKind.Pump:
                    Hint("つないだ範囲の、戦闘できるカードすべての攻撃力・守備力を、ターンの終わりまで変えます（例：巨大化）。" +
                         "守備力が受けているダメージ以下になったカードは破壊されます。範囲で「対象を1つ選ぶ」にすると、選んだ1枚だけになります。");
                    SignedInt("攻撃力の変化", n.Amount, v => n.Amount = v);
                    SignedInt("守備力の変化", n.Amount2, v => n.Amount2 = v);
                    break;
                case NodeKind.Counter:
                    Hint("つないだ範囲の、「フィールド上」でないゾーンのカード（スタックにある呪文など）を、解決させずに墓地へ送ります（打ち消す）。" +
                         "範囲の種類は、インスタントやソーサリーなど、「フィールド上」でないゾーンに置く種類にします。");
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
                    Picker("カードの種類（どれか）", sets.CardTypes, n.Selector.Types);
                    TagPicker("タグ（すべて持つ）", n.Selector.Tags, v => n.Selector.Tags = v);
                    Choice("陣営", new[] { ("お互い", Side.Both), ("自分", Side.Self), ("相手", Side.Opp) }, n.Selector.Side, v => n.Selector.Side = v);
                    Toggle("表側表示のカードだけ", n.Selector.FaceUpOnly, v => n.Selector.FaceUpOnly = v);
                    Toggle("このカード自身を除く", n.Selector.ExcludeSelf, v => n.Selector.ExcludeSelf = v);
                    Choice("マスの関係", new[] { ("条件なし", Near.Any), ("隣のマス", Near.Adjacent), ("同じ縦列", Near.SameColumn) },
                        n.Selector.Near, v => n.Selector.Near = v);
                    Toggle("対象を1つ選ぶ（発動の動きの範囲だけ）", n.Selector.Target, v => n.Selector.Target = v);
                    Hint("対象を1つ選ぶ範囲：解決するときに、範囲に合うカードを1枚選び、そのカードだけに行います（ショック・巨大化・対抗呪文など）。" +
                         "選ばなければ何も起きません。永続効果（無効・攻撃力の変化・守備力の変化）の範囲には使えません。");
                    Hint("マスの関係は、効果を持つカードのマスから見ます（発動した魔法・罠は、置かれていたマス）。「隣」は上下左右、" +
                         "「同じ縦列」は相手の側も含みます。マス目の上にないカードは入りません。無効の範囲にはまだ使えません。");
                    break;
            }
        }
    }
}
