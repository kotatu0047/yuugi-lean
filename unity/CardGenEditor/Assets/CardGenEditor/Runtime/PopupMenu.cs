using System;
using System.Collections.Generic;
using UnityEngine;
using UnityEngine.UIElements;

namespace CardGen.App
{
    /// <summary>メニューの1項目（タイトル・小見出し・区切り・押せる項目）</summary>
    public sealed class MenuEntry
    {
        public string Text;
        /// <summary>項目の下に小さく出す補足（押せないときは、その理由）</summary>
        public string Hint;
        public System.Action Action;
        public bool Enabled = true;
        public bool IsHeader;
        /// <summary>メニューの一番上の帯（何のメニューか）</summary>
        public bool IsTitle;
        public bool IsSeparator;
        /// <summary>押せない情報の行（カードの詳細など）。押せない項目と違って薄くしない</summary>
        public bool IsInfo;
        /// <summary>取り消しにくい操作（削除など）。赤で出す</summary>
        public bool Danger;
        /// <summary>左に出す色の印（ノードの種類の色など）</summary>
        public Color? Swatch;

        public static MenuEntry Item(string text, System.Action action, bool enabled = true, string hint = null,
                                     Color? swatch = null, bool danger = false) =>
            new MenuEntry { Text = text, Action = action, Enabled = enabled && action != null, Hint = hint, Swatch = swatch, Danger = danger };
        public static MenuEntry Header(string text) => new MenuEntry { Text = text, IsHeader = true };
        public static MenuEntry Title(string text, string hint = null, Color? swatch = null) =>
            new MenuEntry { Text = text, Hint = hint, Swatch = swatch, IsHeader = true, IsTitle = true };
        public static MenuEntry Separator() => new MenuEntry { Text = "", IsSeparator = true, Enabled = false };
        public static MenuEntry Info(string text, string hint = null, Color? swatch = null) =>
            new MenuEntry { Text = text, Hint = hint, Swatch = swatch, IsInfo = true, Enabled = false };
    }

    /// <summary>
    /// 右クリックで出るメニュー（コンテキストメニュー）。画面全体を覆う透明な層の上に、カーソルの位置に出す。
    /// 項目を選ぶか、外側をクリックするか、Esc で閉じる。実行時の UI Toolkit には右クリックのメニューがないので自前で作る
    /// </summary>
    public sealed class PopupMenu : VisualElement
    {
        static readonly Color Back = Theme.Alpha(Theme.Panel, 0.98f);
        static readonly Color TitleBack = Theme.PanelHi;
        static readonly Color Edge = Theme.LineHi;
        static readonly Color Line = Theme.Line;
        static readonly Color Text = Theme.Text;
        static readonly Color Muted = Theme.Muted;
        static readonly Color Hover = Theme.Alpha(Theme.Cyan, 0.13f);
        static readonly Color Accent = Theme.Cyan;
        static readonly Color DangerText = Theme.Red;
        const float Width = 300;

        /// <summary>今出ているメニュー（なければ null。自動テストと動作確認用）</summary>
        public static PopupMenu Current { get; private set; }

        readonly VisualElement frame;
        readonly VisualElement shadow;

        /// <summary>
        /// target を右クリックしたら、build で作った項目のメニューを出す。build は右クリックした位置（パネルの座標）を受け取る。
        /// 項目が空ならメニューは出さない。内側の要素のメニューが先に出たら、外側のメニューは出さない
        /// </summary>
        public static void Attach(VisualElement target, Func<Vector2, List<MenuEntry>> build)
        {
            target.RegisterCallback<PointerDownEvent>(evt =>
            {
                if (evt.button != 1) return;
                // 画面は先に覚えておく。build がカードを選んで描き直すと、target は画面から外れる（panel が null になる）
                var root = target.panel?.visualTree;
                if (root == null) return;
                evt.StopPropagation();
                var items = build(evt.position);
                if (items == null || items.Count == 0) return;
                OpenOn(root, evt.position, items);
            });
        }

        /// <summary>anchor が載っている画面の、位置 pos（パネルの座標）にメニューを出す</summary>
        public static PopupMenu Open(VisualElement anchor, Vector2 pos, List<MenuEntry> items)
        {
            var root = anchor.panel?.visualTree;
            return root == null ? null : OpenOn(root, pos, items);
        }

        /// <summary>画面 root の、位置 pos にメニューを出す</summary>
        static PopupMenu OpenOn(VisualElement root, Vector2 pos, List<MenuEntry> items)
        {
            Current?.Close();
            var m = new PopupMenu(items);
            root.Add(m);
            m.Place(pos, root);
            m.Focus();
            Current = m;
            return m;
        }

        static void Round(IStyle s, float r) => Theme.Round(s, r);

        /// <summary>メニューのタイトル（動作確認用）</summary>
        public string TitleText { get; private set; }

        PopupMenu(List<MenuEntry> items)
        {
            TitleText = items.Find(i => i.IsTitle)?.Text ?? "";
            style.position = Position.Absolute;
            style.left = style.top = 0;
            style.right = style.bottom = 0;
            focusable = true;
            RegisterCallback<PointerDownEvent>(evt =>
            {
                if (evt.target == this) Close();
                evt.StopPropagation();
            });
            RegisterCallback<KeyDownEvent>(evt => { if (evt.keyCode == KeyCode.Escape) Close(); });

            // 影（少しずらした半透明の黒）
            shadow = new VisualElement { pickingMode = PickingMode.Ignore };
            shadow.style.position = Position.Absolute;
            shadow.style.backgroundColor = new Color(0, 0, 0, 0.55f);
            Round(shadow.style, 2);
            Add(shadow);

            frame = new VisualElement();
            frame.style.position = Position.Absolute;
            frame.style.width = Width;
            frame.style.backgroundColor = Back;
            frame.style.borderLeftWidth = frame.style.borderRightWidth = frame.style.borderTopWidth = frame.style.borderBottomWidth = 1;
            frame.style.borderLeftColor = frame.style.borderRightColor = frame.style.borderTopColor = frame.style.borderBottomColor = Edge;
            Round(frame.style, 2);
            frame.style.overflow = Overflow.Hidden;
            var title = items.Find(i => i.IsTitle);
            if (title != null) frame.Add(TitleRow(title));
            var list = new ScrollView(ScrollViewMode.Vertical);
            list.style.paddingTop = 4;
            list.style.paddingBottom = 6;
            list.style.flexShrink = 1;
            foreach (var it in items) if (!it.IsTitle) list.Add(Row(it));
            frame.Add(list);
            frame.Add(Theme.BracketsOverlay(() => Theme.Amber, 11, 2f));
            Add(frame);
        }

        static VisualElement Swatch(Color c, float size)
        {
            var s = new VisualElement { pickingMode = PickingMode.Ignore };
            s.style.width = s.style.height = size;
            s.style.flexShrink = 0;
            s.style.marginRight = 8;
            s.style.backgroundColor = c;
            Round(s.style, 3);
            return s;
        }

        static Label Lbl(string text, float size, Color color, bool bold = false)
        {
            var l = new Label(text) { pickingMode = PickingMode.Ignore };
            l.style.fontSize = size;
            l.style.color = color;
            l.style.whiteSpace = WhiteSpace.Normal;
            l.style.marginLeft = l.style.marginRight = l.style.marginTop = l.style.marginBottom = 0;
            l.style.paddingLeft = l.style.paddingRight = l.style.paddingTop = l.style.paddingBottom = 0;
            if (bold) l.style.unityFontStyleAndWeight = FontStyle.Bold;
            return l;
        }

        static VisualElement TitleRow(MenuEntry it)
        {
            var row = new VisualElement();
            row.style.flexDirection = FlexDirection.Row;
            row.style.alignItems = Align.Center;
            row.style.backgroundColor = TitleBack;
            row.style.paddingLeft = 12;
            row.style.paddingRight = 12;
            row.style.paddingTop = 8;
            row.style.paddingBottom = 8;
            row.style.borderBottomWidth = 1;
            row.style.borderBottomColor = Line;
            if (it.Swatch is Color c) row.Add(Swatch(c, 12));
            var col = new VisualElement();
            col.style.flexShrink = 1;
            col.Add(Theme.Tag("ctx // menu", Theme.Alpha(Theme.Cyan, 0.95f), 10));
            col.Add(Lbl(it.Text, 14, Theme.Bright, true));
            if (!string.IsNullOrEmpty(it.Hint)) col.Add(Lbl(it.Hint, 11, Muted));
            row.Add(col);
            return row;
        }

        VisualElement Row(MenuEntry it)
        {
            if (it.IsSeparator)
            {
                var line = new VisualElement();
                line.style.height = 1;
                line.style.marginTop = line.style.marginBottom = 5;
                line.style.marginLeft = line.style.marginRight = 10;
                line.style.backgroundColor = Line;
                return line;
            }
            if (it.IsHeader)
            {
                var h = Lbl(it.Text, 11, Accent, true);
                h.style.paddingLeft = 12;
                h.style.paddingTop = 6;
                h.style.paddingBottom = 2;
                return h;
            }
            var row = new VisualElement();
            row.style.flexDirection = FlexDirection.Row;
            row.style.alignItems = Align.Center;
            row.style.paddingLeft = 9;
            row.style.paddingRight = 12;
            row.style.paddingTop = 5;
            row.style.paddingBottom = 5;
            row.style.borderLeftWidth = 3;
            row.style.borderLeftColor = Color.clear;
            if (it.Swatch is Color c) row.Add(Swatch(c, 10));
            var col = new VisualElement { pickingMode = PickingMode.Ignore };
            col.style.flexShrink = 1;
            col.style.flexGrow = 1;
            col.Add(Lbl(it.Text, it.IsInfo ? 12 : 13, it.Danger ? DangerText : it.IsInfo ? Muted : Text));
            if (!string.IsNullOrEmpty(it.Hint)) col.Add(Lbl(it.Hint, 11, Muted));
            row.Add(col);
            if (it.IsInfo)
            {
                row.style.paddingTop = row.style.paddingBottom = 2;
                return row;
            }
            if (!it.Enabled)
            {
                row.style.opacity = 0.6f;
                return row;
            }
            var action = it.Action;
            row.AddManipulator(new Clickable(() => { Close(); action?.Invoke(); }));
            row.RegisterCallback<PointerEnterEvent>(_ =>
            {
                row.style.backgroundColor = Hover;
                row.style.borderLeftColor = it.Danger ? DangerText : Accent;
            });
            row.RegisterCallback<PointerLeaveEvent>(_ =>
            {
                row.style.backgroundColor = Color.clear;
                row.style.borderLeftColor = Color.clear;
            });
            return row;
        }

        /// <summary>カーソルの位置に置き、画面からはみ出すなら内側に寄せる</summary>
        void Place(Vector2 pos, VisualElement root)
        {
            frame.style.left = pos.x;
            frame.style.top = pos.y;
            frame.style.maxHeight = new Length(85, LengthUnit.Percent);
            frame.RegisterCallback<GeometryChangedEvent>(_ =>
            {
                var w = root.layout.width;
                var h = root.layout.height;
                if (float.IsNaN(w) || float.IsNaN(h)) return;
                var r = frame.layout;
                var x = Mathf.Max(0, Mathf.Min(pos.x, w - r.width - 8));
                var y = Mathf.Max(0, Mathf.Min(pos.y, h - r.height - 8));
                frame.style.left = x;
                frame.style.top = y;
                shadow.style.left = x + 4;
                shadow.style.top = y + 5;
                shadow.style.width = r.width;
                shadow.style.height = r.height;
            });
        }

        public void Close()
        {
            RemoveFromHierarchy();
            if (Current == this) Current = null;
        }

        /// <summary>項目の文字（区切りを除く。タイトルと小見出しも含む。自動テスト用）</summary>
        public static List<string> Texts(List<MenuEntry> items) =>
            items.FindAll(i => !i.IsSeparator).ConvertAll(i => i.Text);

        /// <summary>文字に text を含む押せる項目を選ぶ（なければ false。自動テスト用）</summary>
        public static bool Choose(List<MenuEntry> items, string text)
        {
            var it = items.Find(i => !i.IsHeader && !i.IsSeparator && !i.IsInfo && i.Enabled && i.Text.Contains(text));
            if (it == null) return false;
            it.Action();
            return true;
        }
    }
}
