using UnityEngine;
using UnityEngine.TextCore.Text;
using UnityEngine.UIElements;

namespace CardGen.App
{
    /// <summary>
    /// 画面の見た目（SF 映画の画面のような HUD 風）：配色、英字の小さなラベル、四隅のブラケット、方眼、走査線。
    /// 色はここにまとめ、ほかのファイルはここを参照する（ボタン・入力欄・スクロールバーは CardGenTheme.tss）
    /// </summary>
    public static class Theme
    {
        static Color Rgb(int r, int g, int b, float a = 1) => new Color(r / 255f, g / 255f, b / 255f, a);

        // ---- 配色 ----
        /// <summary>一番奥の背景</summary>
        public static readonly Color Void = Rgb(3, 7, 12);
        /// <summary>キャンバスの背景</summary>
        public static readonly Color Deep = Rgb(5, 12, 19);
        /// <summary>パネルの背景（少し透ける）</summary>
        public static readonly Color Panel = Rgb(8, 19, 29, 0.94f);
        /// <summary>パネルの中の一段明るい背景（見出しの帯など）</summary>
        public static readonly Color PanelHi = Rgb(12, 30, 45, 0.96f);
        /// <summary>細い線</summary>
        public static readonly Color Line = Rgb(0, 229, 255, 0.26f);
        /// <summary>目立つ線</summary>
        public static readonly Color LineHi = Rgb(0, 229, 255, 0.55f);
        /// <summary>主な強調（シアン）</summary>
        public static readonly Color Cyan = Rgb(0, 229, 255);
        /// <summary>注意・選択（アンバー）</summary>
        public static readonly Color Amber = Rgb(255, 184, 0);
        /// <summary>危険・問題（赤）</summary>
        public static readonly Color Red = Rgb(255, 64, 96);
        /// <summary>成功・有効（緑）</summary>
        public static readonly Color Green = Rgb(64, 255, 160);
        /// <summary>本文</summary>
        public static readonly Color Text = Rgb(214, 240, 255);
        /// <summary>見出しの白</summary>
        public static readonly Color Bright = Rgb(235, 250, 255);
        /// <summary>補足</summary>
        public static readonly Color Muted = Rgb(156, 190, 210);
        /// <summary>さらに控えめな文字（マスの番号など）</summary>
        public static readonly Color Dim = Rgb(118, 150, 170);

        /// <summary>a に透明度 alpha をかけた色</summary>
        public static Color Alpha(Color c, float alpha) => new Color(c.r, c.g, c.b, alpha);

        /// <summary>ノードの種類の色（ネオン調）</summary>
        public static Color Kind(NodeKind k) => k switch
        {
            NodeKind.Rules => Rgb(176, 124, 255),
            NodeKind.Zone => Rgb(60, 168, 255),
            NodeKind.Card => Rgb(255, 184, 0),
            NodeKind.Activate => Rgb(255, 128, 64),
            NodeKind.Trigger => Rgb(255, 222, 120),
            NodeKind.Destroy => Rgb(255, 72, 96),
            NodeKind.Bounce => Rgb(80, 210, 255),
            NodeKind.Draw => Rgb(236, 224, 84),
            NodeKind.Negate => Rgb(64, 232, 144),
            NodeKind.Boost => Rgb(0, 224, 200),
            NodeKind.Toughen => Rgb(124, 168, 255),
            NodeKind.Strike => Rgb(255, 112, 80),
            NodeKind.Pump => Rgb(168, 244, 72),
            NodeKind.Counter => Rgb(160, 150, 255),
            NodeKind.Damage => Rgb(255, 84, 176),
            NodeKind.Heal => Rgb(84, 244, 124),
            NodeKind.Axioms => Rgb(164, 200, 220),
            NodeKind.Sets => Rgb(0, 204, 172),
            _ => Rgb(186, 206, 222),
        };

        // ---- 文字 ----

        static FontDefinition? display;
        static bool displayLoaded;

        /// <summary>英字の小さなラベルの字体（Windows の Bahnschrift。なければ普通の字体）</summary>
        public static FontDefinition? Display
        {
            get
            {
                if (displayLoaded) return display;
                displayLoaded = true;
                foreach (var family in new[] { "Bahnschrift", "Bahnschrift SemiCondensed", "Consolas" })
                {
                    try
                    {
                        var fa = FontAsset.CreateFontAsset(family, "Regular");
                        if (fa == null) continue;
                        display = FontDefinition.FromSDFFont(fa);
                        break;
                    }
                    catch (System.Exception) { }
                }
                return display;
            }
        }

        /// <summary>英字の小さなラベル（例：「SYS // EDITOR」）。字間を広げ、大文字で出す（読めるように 10 より小さくはしない）</summary>
        public static Label Tag(string text, Color? color = null, float size = 10)
        {
            size = Mathf.Max(size, 10);
            var l = new Label(text.ToUpperInvariant()) { pickingMode = PickingMode.Ignore };
            l.style.fontSize = size;
            l.style.color = color ?? Muted;
            l.style.letterSpacing = size * 0.22f;
            l.style.marginLeft = l.style.marginRight = l.style.marginTop = l.style.marginBottom = 0;
            l.style.paddingLeft = l.style.paddingRight = l.style.paddingTop = l.style.paddingBottom = 0;
            if (Display is FontDefinition f) l.style.unityFontDefinition = f;
            return l;
        }

        /// <summary>
        /// 見出し：左に光る短い棒、日本語の見出し、右に英字のタグ、下に細い線
        /// </summary>
        public static VisualElement Heading(string text, string tag = null, Color? color = null, float size = 13)
        {
            var c = color ?? Cyan;
            var row = new VisualElement { pickingMode = PickingMode.Ignore };
            row.style.flexDirection = FlexDirection.Row;
            row.style.alignItems = Align.Center;
            row.style.marginTop = 12;
            row.style.marginBottom = 5;
            row.style.paddingBottom = 3;
            row.style.borderBottomWidth = 1;
            row.style.borderBottomColor = Line;
            var bar = new VisualElement { pickingMode = PickingMode.Ignore };
            bar.style.width = 3;
            bar.style.height = size + 2;
            bar.style.marginRight = 7;
            bar.style.backgroundColor = c;
            row.Add(bar);
            var l = new Label(text) { pickingMode = PickingMode.Ignore };
            l.style.fontSize = size;
            l.style.color = Bright;
            l.style.unityFontStyleAndWeight = FontStyle.Bold;
            l.style.flexGrow = 1;
            l.style.flexShrink = 1;
            l.style.whiteSpace = WhiteSpace.Normal;
            row.Add(l);
            if (tag != null) row.Add(Tag(tag, Alpha(c, 0.95f), 10));
            return row;
        }

        // ---- 枠と飾り ----

        /// <summary>四辺の線の太さと色</summary>
        public static void Border(IStyle s, float width, Color c)
        {
            s.borderLeftWidth = s.borderRightWidth = s.borderTopWidth = s.borderBottomWidth = width;
            s.borderLeftColor = s.borderRightColor = s.borderTopColor = s.borderBottomColor = c;
        }

        /// <summary>角の丸み</summary>
        public static void Round(IStyle s, float r) =>
            s.borderTopLeftRadius = s.borderTopRightRadius = s.borderBottomLeftRadius = s.borderBottomRightRadius = r;

        /// <summary>四隅の L 字のブラケットを描く（要素の背景の上、子の下）。色は呼ぶたびに変えられる</summary>
        public static void Brackets(VisualElement e, System.Func<Color> color, float length = 9, float width = 1.6f, float inset = 0)
        {
            e.generateVisualContent += ctx =>
            {
                // 描く座標は要素の左上が原点（枠線を含む大きさ）
                var w = e.layout.width;
                var h = e.layout.height;
                if (float.IsNaN(w) || float.IsNaN(h) || w <= 0 || h <= 0) return;
                float x0 = inset, y0 = inset, x1 = w - inset, y1 = h - inset;
                var p = ctx.painter2D;
                p.strokeColor = color();
                p.lineWidth = width;
                p.lineCap = LineCap.Butt;
                void L(Vector2 a, Vector2 b, Vector2 c)
                {
                    p.BeginPath();
                    p.MoveTo(a);
                    p.LineTo(b);
                    p.LineTo(c);
                    p.Stroke();
                }
                L(new Vector2(x0, y0 + length), new Vector2(x0, y0), new Vector2(x0 + length, y0));
                L(new Vector2(x1 - length, y0), new Vector2(x1, y0), new Vector2(x1, y0 + length));
                L(new Vector2(x1, y1 - length), new Vector2(x1, y1), new Vector2(x1 - length, y1));
                L(new Vector2(x0 + length, y1), new Vector2(x0, y1), new Vector2(x0, y1 - length));
            };
        }

        /// <summary>
        /// 四隅のブラケットを、子の上に重ねる層として作る（見出しの帯など、背景のある子に隠れないように）。
        /// 返した要素を、親の最後の子として加える
        /// </summary>
        public static VisualElement BracketsOverlay(System.Func<Color> color, float length = 9, float width = 1.6f)
        {
            var o = new VisualElement { name = "brackets", pickingMode = PickingMode.Ignore };
            o.style.position = Position.Absolute;
            o.style.left = o.style.top = 0;
            o.style.right = o.style.bottom = 0;
            Brackets(o, color, length, width);
            return o;
        }

        /// <summary>HUD のパネル：透ける背景、細い線の枠、四隅のブラケット</summary>
        public static void Frame(VisualElement e, Color? border = null, Color? bg = null, Color? brackets = null)
        {
            e.style.backgroundColor = bg ?? Panel;
            Border(e.style, 1, border ?? Line);
            Round(e.style, 2);
            var b = brackets ?? Alpha(Cyan, 0.75f);
            Brackets(e, () => b);
        }

        /// <summary>方眼（細い線と、5マスごとの少し明るい線）を描く要素。大きさは親に合わせる</summary>
        public static VisualElement Grid(float step = 24, int major = 5)
        {
            var g = new VisualElement { name = "grid", pickingMode = PickingMode.Ignore };
            g.style.position = Position.Absolute;
            g.style.left = g.style.top = 0;
            g.style.right = g.style.bottom = 0;
            g.generateVisualContent += ctx =>
            {
                var r = g.contentRect;
                var p = ctx.painter2D;
                p.lineWidth = 1;
                int i = 0;
                for (float x = 0; x <= r.width; x += step, i++)
                {
                    p.strokeColor = i % major == 0 ? Alpha(Cyan, 0.09f) : Alpha(Cyan, 0.035f);
                    p.BeginPath(); p.MoveTo(new Vector2(x, 0)); p.LineTo(new Vector2(x, r.height)); p.Stroke();
                }
                i = 0;
                for (float y = 0; y <= r.height; y += step, i++)
                {
                    p.strokeColor = i % major == 0 ? Alpha(Cyan, 0.09f) : Alpha(Cyan, 0.035f);
                    p.BeginPath(); p.MoveTo(new Vector2(0, y)); p.LineTo(new Vector2(r.width, y)); p.Stroke();
                }
                // 5マスごとの交点に小さな十字
                p.strokeColor = Alpha(Cyan, 0.22f);
                for (float x = 0; x <= r.width; x += step * major)
                    for (float y = 0; y <= r.height; y += step * major)
                    {
                        p.BeginPath(); p.MoveTo(new Vector2(x - 3, y)); p.LineTo(new Vector2(x + 3, y)); p.Stroke();
                        p.BeginPath(); p.MoveTo(new Vector2(x, y - 3)); p.LineTo(new Vector2(x, y + 3)); p.Stroke();
                    }
            };
            return g;
        }

        /// <summary>画面全体に重ねる、うっすらとした走査線（クリックは下に通す）</summary>
        public static VisualElement Scanlines()
        {
            var s = new VisualElement { name = "scanlines", pickingMode = PickingMode.Ignore };
            s.style.position = Position.Absolute;
            s.style.left = s.style.top = 0;
            s.style.right = s.style.bottom = 0;
            s.generateVisualContent += ctx =>
            {
                var r = s.contentRect;
                var p = ctx.painter2D;
                p.lineWidth = 1;
                p.strokeColor = new Color(0, 0, 0, 0.16f);
                for (float y = 0; y < r.height; y += 3)
                {
                    p.BeginPath(); p.MoveTo(new Vector2(0, y)); p.LineTo(new Vector2(r.width, y)); p.Stroke();
                }
            };
            s.RegisterCallback<GeometryChangedEvent>(_ => s.MarkDirtyRepaint());
            return s;
        }

        /// <summary>小さな点（状態の表示）</summary>
        public static VisualElement Dot(Color c, float size = 7)
        {
            var d = new VisualElement { pickingMode = PickingMode.Ignore };
            d.style.width = d.style.height = size;
            d.style.flexShrink = 0;
            d.style.backgroundColor = c;
            Round(d.style, size / 2);
            return d;
        }
    }
}
