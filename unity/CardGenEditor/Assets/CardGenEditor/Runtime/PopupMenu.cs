using System;
using System.Collections.Generic;
using UnityEngine;
using UnityEngine.UIElements;

namespace CardGen.App
{
    /// <summary>メニューの1項目（見出し・区切り・押せる項目）</summary>
    public sealed class MenuEntry
    {
        public string Text;
        public System.Action Action;
        public bool Enabled = true;
        public bool IsHeader;
        public bool IsSeparator;

        public static MenuEntry Item(string text, System.Action action, bool enabled = true) =>
            new MenuEntry { Text = text, Action = action, Enabled = enabled && action != null };
        public static MenuEntry Header(string text) => new MenuEntry { Text = text, IsHeader = true };
        public static MenuEntry Separator() => new MenuEntry { IsSeparator = true };
    }

    /// <summary>
    /// 右クリックで出るメニュー（コンテキストメニュー）。画面全体を覆う透明な層の上に、カーソルの位置に出す。
    /// 項目を選ぶか、外側をクリックするか、Esc で閉じる。実行時の UI Toolkit には右クリックのメニューがないので自前で作る
    /// </summary>
    public sealed class PopupMenu : VisualElement
    {
        static readonly Color Back = new Color(0.17f, 0.17f, 0.2f, 0.98f);
        static readonly Color Edge = new Color(0.36f, 0.36f, 0.42f);
        static readonly Color Muted = new Color(0.65f, 0.65f, 0.72f);
        static readonly Color Hover = new Color(0.3f, 0.32f, 0.42f);

        /// <summary>今出ているメニュー（なければ null。自動テストと動作確認用）</summary>
        public static PopupMenu Current { get; private set; }

        readonly VisualElement box;

        /// <summary>
        /// target を右クリックしたら、build で作った項目のメニューを出す。build は右クリックした位置（パネルの座標）を受け取る。
        /// 項目が空ならメニューは出さない。内側の要素のメニューが先に出たら、外側のメニューは出さない
        /// </summary>
        public static void Attach(VisualElement target, Func<Vector2, List<MenuEntry>> build)
        {
            target.RegisterCallback<PointerDownEvent>(evt =>
            {
                if (evt.button != 1) return;
                var items = build(evt.position);
                if (items == null || items.Count == 0) return;
                Open(target, evt.position, items);
                evt.StopPropagation();
            });
        }

        /// <summary>anchor が載っている画面の、位置 pos（パネルの座標）にメニューを出す</summary>
        public static PopupMenu Open(VisualElement anchor, Vector2 pos, List<MenuEntry> items)
        {
            Current?.Close();
            var root = anchor.panel?.visualTree;
            if (root == null) return null;
            var m = new PopupMenu(items);
            root.Add(m);
            m.Place(pos, root);
            m.Focus();
            Current = m;
            return m;
        }

        PopupMenu(List<MenuEntry> items)
        {
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

            box = new ScrollView(ScrollViewMode.Vertical);
            box.style.position = Position.Absolute;
            box.style.minWidth = 200;
            box.style.maxWidth = 460;
            box.style.backgroundColor = Back;
            box.style.paddingTop = box.style.paddingBottom = 4;
            box.style.borderLeftWidth = box.style.borderRightWidth = box.style.borderTopWidth = box.style.borderBottomWidth = 1;
            box.style.borderLeftColor = box.style.borderRightColor = box.style.borderTopColor = box.style.borderBottomColor = Edge;
            box.style.borderTopLeftRadius = box.style.borderTopRightRadius =
                box.style.borderBottomLeftRadius = box.style.borderBottomRightRadius = 6;
            foreach (var it in items) box.Add(Row(it));
            Add(box);
        }

        VisualElement Row(MenuEntry it)
        {
            if (it.IsSeparator)
            {
                var line = new VisualElement();
                line.style.height = 1;
                line.style.marginTop = line.style.marginBottom = 4;
                line.style.backgroundColor = Edge;
                return line;
            }
            if (it.IsHeader)
            {
                var h = new Label(it.Text);
                h.style.fontSize = 10;
                h.style.color = Muted;
                h.style.paddingLeft = 10;
                h.style.paddingTop = 2;
                h.style.unityFontStyleAndWeight = FontStyle.Bold;
                return h;
            }
            var action = it.Action;
            var b = UiTest.Btn(it.Text, () => { Close(); action?.Invoke(); });
            b.SetEnabled(it.Enabled);
            b.style.unityTextAlign = TextAnchor.MiddleLeft;
            b.style.whiteSpace = WhiteSpace.Normal;
            b.style.marginLeft = b.style.marginRight = b.style.marginTop = b.style.marginBottom = 0;
            b.style.paddingLeft = 10;
            b.style.paddingRight = 14;
            b.style.paddingTop = b.style.paddingBottom = 3;
            b.style.borderLeftWidth = b.style.borderRightWidth = b.style.borderTopWidth = b.style.borderBottomWidth = 0;
            b.style.borderTopLeftRadius = b.style.borderTopRightRadius = b.style.borderBottomLeftRadius = b.style.borderBottomRightRadius = 0;
            b.style.backgroundColor = Color.clear;
            b.RegisterCallback<PointerEnterEvent>(_ => { if (b.enabledSelf) b.style.backgroundColor = Hover; });
            b.RegisterCallback<PointerLeaveEvent>(_ => b.style.backgroundColor = Color.clear);
            return b;
        }

        /// <summary>カーソルの位置に置き、画面からはみ出すなら内側に寄せる</summary>
        void Place(Vector2 pos, VisualElement root)
        {
            box.style.left = pos.x;
            box.style.top = pos.y;
            box.style.maxHeight = new Length(80, LengthUnit.Percent);
            box.RegisterCallback<GeometryChangedEvent>(_ =>
            {
                var w = root.layout.width;
                var h = root.layout.height;
                if (float.IsNaN(w) || float.IsNaN(h)) return;
                var r = box.layout;
                box.style.left = Mathf.Max(0, Mathf.Min(pos.x, w - r.width - 4));
                box.style.top = Mathf.Max(0, Mathf.Min(pos.y, h - r.height - 4));
            });
        }

        public void Close()
        {
            RemoveFromHierarchy();
            if (Current == this) Current = null;
        }

        /// <summary>項目の文字（区切りを除く。見出しも含む。自動テスト用）</summary>
        public static List<string> Texts(List<MenuEntry> items) =>
            items.FindAll(i => !i.IsSeparator).ConvertAll(i => i.Text);

        /// <summary>文字に text を含む押せる項目を選ぶ（なければ false。自動テスト用）</summary>
        public static bool Choose(List<MenuEntry> items, string text)
        {
            var it = items.Find(i => !i.IsHeader && !i.IsSeparator && i.Enabled && i.Text.Contains(text));
            if (it == null) return false;
            it.Action();
            return true;
        }
    }
}
