using System;
using System.Collections.Generic;
using System.Linq;
using UnityEngine;
using UnityEngine.UIElements;

namespace CardGen.App
{
    /// <summary>
    /// ノードを並べてつなぐキャンバス（背景のドラッグで移動、ホイールで拡大縮小）。
    /// ノードの右の丸にカーソルを合わせる（またはクリックする）と、つなげるノードの候補が出て、選ぶとつないだ状態で加わる。
    /// 右クリックでメニューを出す（ノードの上：つなぐ・表示・つなぎを外す・削除、空き場所：ノードを加える・整列・表示を戻す）
    /// </summary>
    public sealed class GraphCanvas : VisualElement
    {
        public GraphDoc Doc { get; private set; } = new GraphDoc();
        public event Action<Node> Selected;
        public event System.Action Changed;

        readonly VisualElement content;
        readonly VisualElement edgeLayer;
        // つなぎ線の上を流れる光の点（毎フレーム描き直すので、線とは別の層にする）
        readonly VisualElement flowLayer;
        float clock;
        readonly Dictionary<int, NodeView> views = new Dictionary<int, NodeView>();
        Vector2 offset = new Vector2(20, 20);
        float zoom = 0.85f;
        Node selected;
        HashSet<int> problems = new HashSet<int>();

        // ドラッグの状態
        enum Drag { None, Pan, Move, Connect }
        Drag drag;
        Vector2 dragStart;
        Vector2 dragOrigin;
        NodeView dragNode;
        Vector2 connectEnd;

        // つなぎ先の候補の一覧
        readonly VisualElement popup;
        NodeView popupFor;
        bool overPopup, overPort;

        public GraphCanvas()
        {
            style.flexGrow = 1;
            style.overflow = Overflow.Hidden;
            style.backgroundColor = Theme.Deep;
            focusable = true;

            content = new VisualElement { name = "content", pickingMode = PickingMode.Ignore };
            content.style.position = Position.Absolute;
            content.style.left = 0;
            content.style.top = 0;
            content.style.width = 4000;
            content.style.height = 4000;
            content.style.transformOrigin = new TransformOrigin(0, 0);
            Add(content);
            // 方眼（キャンバスと一緒に動き、拡大縮小する）
            content.Add(Theme.Grid());

            edgeLayer = new VisualElement { name = "edges", pickingMode = PickingMode.Ignore };
            edgeLayer.style.position = Position.Absolute;
            edgeLayer.style.left = 0;
            edgeLayer.style.top = 0;
            edgeLayer.style.width = 4000;
            edgeLayer.style.height = 4000;
            edgeLayer.generateVisualContent += DrawEdges;
            content.Add(edgeLayer);

            flowLayer = new VisualElement { name = "flow", pickingMode = PickingMode.Ignore };
            flowLayer.style.position = Position.Absolute;
            flowLayer.style.left = 0;
            flowLayer.style.top = 0;
            flowLayer.style.width = 4000;
            flowLayer.style.height = 4000;
            flowLayer.generateVisualContent += DrawFlow;
            content.Add(flowLayer);
            // 動き：選んでいるノードの明滅と、流れる点（画面に出ているときだけ）
            schedule.Execute(Tick).Every(33);

            popup = new VisualElement { name = "candidates" };
            popup.style.position = Position.Absolute;
            popup.style.display = DisplayStyle.None;
            Theme.Frame(popup, Theme.LineHi, Theme.Panel, Theme.Amber);
            popup.style.paddingLeft = popup.style.paddingRight = 8;
            popup.style.paddingTop = popup.style.paddingBottom = 8;
            popup.RegisterCallback<PointerEnterEvent>(_ => overPopup = true);
            popup.RegisterCallback<PointerLeaveEvent>(_ => { overPopup = false; HideSoon(); });
            Add(popup);

            RegisterCallback<PointerDownEvent>(OnDown);
            RegisterCallback<PointerMoveEvent>(OnMove);
            RegisterCallback<PointerUpEvent>(OnUp);
            RegisterCallback<WheelEvent>(OnWheel);
            ApplyTransform();
        }

        public void SetDoc(GraphDoc doc)
        {
            Doc = doc;
            selected = null;
            Rebuild();
        }

        public void Rebuild()
        {
            foreach (var v in views.Values) v.RemoveFromHierarchy();
            views.Clear();
            foreach (var n in Doc.Nodes)
            {
                var v = new NodeView(n);
                views[n.Id] = v;
                content.Add(v);
                v.SetSelected(n == selected);
                v.SetProblem(problems.Contains(n.Id));
                if (GraphDoc.Candidates(n.Kind).Count > 0)
                {
                    v.OutPort.RegisterCallback<PointerEnterEvent>(_ => { overPort = true; ShowCandidates(v); });
                    v.OutPort.RegisterCallback<PointerLeaveEvent>(_ => { overPort = false; HideSoon(); });
                    v.OutPort.tooltip = "つなげるノードの候補を出す（ドラッグで、別のノードにつなぐこともできる）";
                }
            }
            HideCandidates();
            edgeLayer.MarkDirtyRepaint();
        }

        /// <summary>ノード v の右の丸のそばに、つなげるノードの候補を出す</summary>
        void ShowCandidates(NodeView v)
        {
            popupFor = v;
            popup.Clear();
            popup.Add(Theme.Tag("link // candidates", Theme.Alpha(Theme.Cyan, 0.7f), 9));
            var head = new Label($"{v.Node.Title} につなぐ") { style = { fontSize = 12, color = Theme.Bright, marginBottom = 4, unityFontStyleAndWeight = FontStyle.Bold } };
            popup.Add(head);
            foreach (var k in GraphDoc.Candidates(v.Node.Kind))
            {
                var kind = k;
                var b = UiTest.Btn(Node.KindLabel(kind), () => AddCandidate(kind));
                b.style.marginLeft = b.style.marginRight = 0;
                b.style.marginTop = b.style.marginBottom = 1;
                b.style.unityTextAlign = TextAnchor.MiddleLeft;
                b.style.borderLeftWidth = 4;
                b.style.borderLeftColor = NodeView.KindColor(kind);
                popup.Add(b);
            }
            if (Node.TakesSelector(v.Node.Kind) && Doc.Children(v.Node).Count > 0)
                popup.Add(new Label("（今の範囲と入れ替わります）") { style = { fontSize = 10, color = Theme.Muted } });
            var port = v.OutPort.worldBound;
            var local = this.WorldToLocal(new Vector2(port.xMax + 6, port.yMin - 4));
            popup.style.left = Mathf.Min(local.x, Mathf.Max(0, layout.width - 200));
            popup.style.top = Mathf.Max(0, local.y);
            popup.style.display = DisplayStyle.Flex;
            popup.BringToFront();
        }

        /// <summary>つなぎ先の候補の一覧（自動テスト用。UiTest.Press でボタンを押せる）</summary>
        public VisualElement CandidatePopup => popup;
        /// <summary>候補の一覧が出ているか</summary>
        public bool CandidatesShown => popup.style.display == DisplayStyle.Flex;

        /// <summary>ノード n のつなぎ先の候補を出す（動作確認用）</summary>
        public void ShowCandidatesFor(Node n)
        {
            if (views.TryGetValue(n.Id, out var v)) { overPort = true; ShowCandidates(v); }
        }

        void HideCandidates()
        {
            popup.style.display = DisplayStyle.None;
            popupFor = null;
            overPopup = false;
        }

        /// <summary>カーソルが丸からも一覧からも離れたら、少し待って閉じる</summary>
        void HideSoon() => schedule.Execute(() => { if (!overPopup && !overPort) HideCandidates(); }).ExecuteLater(300);

        static float HeightOf(NodeView v) => float.IsNaN(v.layout.height) || v.layout.height <= 0 ? 100 : v.layout.height;
        static float WidthOf(NodeView v) => float.IsNaN(v.layout.width) || v.layout.width <= 0 ? NodeView.Width : v.layout.width;

        /// <summary>候補を選んだ：親の右の列に、つないだ状態で加える</summary>
        void AddCandidate(NodeKind kind)
        {
            if (popupFor != null) AddChildOf(popupFor.Node, kind);
        }

        /// <summary>parent の右の列に、kind のノードをつないだ状態で加える</summary>
        public Node AddChildOf(Node parent, NodeKind kind)
        {
            var pw = views.TryGetValue(parent.Id, out var pv) ? WidthOf(pv) : NodeView.Width;
            var n = Doc.AddChild(parent, kind, x => views.TryGetValue(x.Id, out var nv) ? HeightOf(nv) : 100, pw);
            Rebuild();
            Select(n);
            Changed?.Invoke();
            return n;
        }

        // ---- 右クリックのメニュー ----

        /// <summary>ノード n の右クリックのメニュー：つなげるノード・表示・つなぎを外す・削除</summary>
        public List<MenuEntry> NodeMenu(Node n)
        {
            var items = new List<MenuEntry> { MenuEntry.Title(n.Title, n.Title == Node.KindLabel(n.Kind) ? null : Node.KindLabel(n.Kind), NodeView.KindColor(n.Kind)) };
            var cands = GraphDoc.Candidates(n.Kind);
            if (cands.Count > 0)
            {
                items.Add(MenuEntry.Header("つなげるノード（右に加わる）"));
                var replaces = Node.TakesSelector(n.Kind) && Doc.Children(n).Count > 0;
                foreach (var k in cands)
                {
                    var kind = k;
                    items.Add(MenuEntry.Item(Node.KindLabel(kind), () => AddChildOf(n, kind),
                        hint: replaces && kind == NodeKind.Selector ? "今の範囲と入れ替わります" : null, swatch: NodeView.KindColor(kind)));
                }
                items.Add(MenuEntry.Separator());
            }
            items.Add(MenuEntry.Header("このノード"));
            items.Add(MenuEntry.Item("左上に表示する", () => Focus(n)));
            var connected = Doc.Edges.Any(e => e.To == n.Id);
            items.Add(MenuEntry.Item("入ってくるつなぎを外す", () => Disconnect(n), connected, connected ? null : "どこからもつながっていません"));
            items.Add(MenuEntry.Item("削除", () => { Select(n); RemoveSelected(); }, !Node.IsFixed(n.Kind),
                Node.IsFixed(n.Kind) ? "公理と集合は削除できません" : "つないだ線も消えます", danger: true));
            return items;
        }

        /// <summary>キャンバスの空き場所（キャンバスの座標 at）の右クリックのメニュー：ノードを加える・整列・表示を戻す</summary>
        public List<MenuEntry> BackgroundMenu(Vector2 at)
        {
            var items = new List<MenuEntry>
            {
                MenuEntry.Title("キャンバス", $"ノード {Doc.Nodes.Count} 個"),
                MenuEntry.Header("ここにノードを加える"),
            };
            foreach (NodeKind k in Enum.GetValues(typeof(NodeKind)))
            {
                if (k == NodeKind.Rules || Node.IsFixed(k)) continue;
                var kind = k;
                items.Add(MenuEntry.Item(Node.KindLabel(kind), () => AddNodeAt(kind, at), swatch: NodeView.KindColor(kind)));
            }
            items.Add(MenuEntry.Separator());
            items.Add(MenuEntry.Header("表示"));
            items.Add(MenuEntry.Item("整列", Arrange, hint: "木の形に並べ直す（つないだ先は右の列）"));
            items.Add(MenuEntry.Item("表示を元に戻す", ResetView, hint: "位置と拡大率"));
            return items;
        }

        /// <summary>キャンバスの座標 at に kind のノードを加える（どこにもつながない）</summary>
        public Node AddNodeAt(NodeKind kind, Vector2 at)
        {
            var n = Node.Make(Doc.NextId, kind, at.x, at.y);
            Doc.Nodes.Add(n);
            Rebuild();
            Select(n);
            Changed?.Invoke();
            return n;
        }

        /// <summary>n に入ってくるつなぎを外す</summary>
        public void Disconnect(Node n)
        {
            Doc.Edges.RemoveAll(e => e.To == n.Id);
            edgeLayer.MarkDirtyRepaint();
            Changed?.Invoke();
        }

        /// <summary>位置と拡大率を最初の状態に戻す</summary>
        public void ResetView()
        {
            offset = new Vector2(20, 20);
            zoom = 0.85f;
            ApplyTransform();
        }

        /// <summary>ノード n のメニューを、そのノードの右上に出す（動作確認用）</summary>
        public void OpenMenuFor(Node n)
        {
            if (!views.TryGetValue(n.Id, out var v)) return;
            Select(n);
            PopupMenu.Open(this, new Vector2(v.worldBound.xMax - 40, v.worldBound.yMin + 20), NodeMenu(n));
        }

        void OpenMenu(PointerDownEvent evt)
        {
            HideCandidates();
            var nv = NodeAt(evt.position);
            if (nv != null) Select(nv.Node);
            var items = nv != null ? NodeMenu(nv.Node) : BackgroundMenu(ToContent(this.WorldToLocal(evt.position)));
            PopupMenu.Open(this, evt.position, items);
        }

        /// <summary>木の形に並べ直す（親の右に子、子は上から順）</summary>
        public void Arrange()
        {
            Doc.AutoLayout(n => views.TryGetValue(n.Id, out var v) ? HeightOf(v) : 100,
                           n => views.TryGetValue(n.Id, out var v) ? WidthOf(v) : NodeView.Width);
            foreach (var v in views.Values) v.Refresh();
            edgeLayer.MarkDirtyRepaint();
            Changed?.Invoke();
        }

        public void RefreshNode(Node n)
        {
            if (views.TryGetValue(n.Id, out var v)) v.Refresh();
            edgeLayer.MarkDirtyRepaint();
        }

        public void SetProblems(IEnumerable<int> ids)
        {
            problems = new HashSet<int>(ids);
            foreach (var kv in views) kv.Value.SetProblem(problems.Contains(kv.Key));
        }

        public void Select(Node n)
        {
            selected = n;
            foreach (var v in views.Values) v.SetSelected(v.Node == n);
            Selected?.Invoke(n);
        }

        public Node SelectedNode => selected;

        /// <summary>画面の真ん中あたりに新しいノードを置く</summary>
        public Node AddNode(NodeKind kind)
        {
            var center = ToContent(new Vector2(layout.width * 0.4f, layout.height * 0.35f));
            var n = Node.Make(Doc.NextId, kind, center.x + (Doc.Nodes.Count % 5) * 12, center.y + (Doc.Nodes.Count % 5) * 12);
            Doc.Nodes.Add(n);
            // 選んでいるノードからつなげるなら、つないでおく
            if (selected != null && GraphDoc.CanConnect(selected.Kind, kind)) Doc.Connect(selected.Id, n.Id);
            Rebuild();
            Select(n);
            Changed?.Invoke();
            return n;
        }

        public void RemoveSelected()
        {
            if (selected == null || Node.IsFixed(selected.Kind)) return;
            Doc.Remove(selected.Id);
            selected = null;
            Rebuild();
            Selected?.Invoke(null);
            Changed?.Invoke();
        }

        /// <summary>ノードが画面の左上寄りに来るように動かす</summary>
        public void Focus(Node n)
        {
            offset = new Vector2(80, 80) - new Vector2(n.X, n.Y) * zoom;
            ApplyTransform();
        }

        Vector2 ToContent(Vector2 local) => (local - offset) / zoom;

        void ApplyTransform()
        {
            content.style.translate = new Translate(offset.x, offset.y);
            content.style.scale = new Scale(new Vector3(zoom, zoom, 1));
        }

        static Vector2 OutPos(Node n) => new Vector2(n.X + NodeView.Width, n.Y + NodeView.HeaderHeight / 2);
        static Vector2 InPos(Node n) => new Vector2(n.X, n.Y + NodeView.HeaderHeight / 2);

        /// <summary>つなぎ線の曲線の制御点（a から b へ、水平に出て水平に入る）</summary>
        static (Vector2, Vector2) Controls(Vector2 a, Vector2 b)
        {
            float dx = Mathf.Max(40, Mathf.Abs(b.x - a.x) * 0.5f);
            return (a + new Vector2(dx, 0), b - new Vector2(dx, 0));
        }

        static Vector2 Bezier(Vector2 a, Vector2 c1, Vector2 c2, Vector2 b, float t)
        {
            float u = 1 - t;
            return u * u * u * a + 3 * u * u * t * c1 + 3 * u * t * t * c2 + t * t * t * b;
        }

        void Tick()
        {
            if (panel == null || resolvedStyle.display == DisplayStyle.None || layout.width <= 0) return;
            clock = Time.realtimeSinceStartup;
            flowLayer.MarkDirtyRepaint();
            if (selected != null && views.TryGetValue(selected.Id, out var v)) v.Pulse(clock);
        }

        /// <summary>
        /// 流れる光の点：つなぎ線ごとに2つ、親から子へ流れる（尾を引く）。線ごとに少しずらす
        /// </summary>
        void DrawFlow(MeshGenerationContext ctx)
        {
            var p = ctx.painter2D;
            foreach (var e in Doc.Edges)
            {
                var a = Doc.Find(e.From);
                var b = Doc.Find(e.To);
                if (a == null || b == null) continue;
                Vector2 pa = OutPos(a), pb = InPos(b);
                var (c1, c2) = Controls(pa, pb);
                var col = Color.Lerp(NodeView.KindColor(a.Kind), Color.white, 0.35f);
                float len = Mathf.Max(60, Vector2.Distance(pa, pb));
                float speed = 90f / len;   // 1秒に 90 ほど進む
                float shift = (e.From * 0.37f + e.To * 0.61f) % 1f;
                for (int k = 0; k < 2; k++)
                {
                    float t0 = Mathf.Repeat(clock * speed + shift + k * 0.5f, 1f);
                    for (int j = 4; j >= 0; j--)
                    {
                        float t = t0 - j * 0.018f;
                        if (t < 0) continue;
                        var q = Bezier(pa, c1, c2, pb, t);
                        float fade = 1f - j / 5f;
                        if (j == 0)
                        {
                            p.fillColor = Theme.Alpha(col, 0.22f);
                            p.BeginPath(); p.Arc(q, 5f, 0, 360); p.Fill();
                        }
                        p.fillColor = Theme.Alpha(col, 0.9f * fade);
                        p.BeginPath(); p.Arc(q, j == 0 ? 2.2f : 1.6f * fade + 0.4f, 0, 360); p.Fill();
                    }
                }
            }
        }

        void DrawCurve(Painter2D p, Vector2 a, Vector2 b, Color c)
        {
            // 光る線：太く薄い線の上に、細く明るい線を重ねる。両端に小さな点
            float dx = Mathf.Max(40, Mathf.Abs(b.x - a.x) * 0.5f);
            foreach (var (w, alpha) in new[] { (7f, 0.12f), (3.5f, 0.28f), (1.4f, 1f) })
            {
                p.strokeColor = Theme.Alpha(c, alpha);
                p.lineWidth = w;
                p.BeginPath();
                p.MoveTo(a);
                p.BezierCurveTo(a + new Vector2(dx, 0), b - new Vector2(dx, 0), b);
                p.Stroke();
            }
            p.fillColor = c;
            foreach (var q in new[] { a, b })
            {
                p.BeginPath();
                p.Arc(q, 2.5f, 0, 360);
                p.Fill();
            }
        }

        void DrawEdges(MeshGenerationContext ctx)
        {
            var p = ctx.painter2D;
            foreach (var e in Doc.Edges)
            {
                var a = Doc.Find(e.From);
                var b = Doc.Find(e.To);
                if (a == null || b == null) continue;
                DrawCurve(p, OutPos(a), InPos(b), NodeView.KindColor(a.Kind));
            }
            if (drag == Drag.Connect && dragNode != null)
                DrawCurve(p, OutPos(dragNode.Node), connectEnd, Theme.Amber);
        }

        NodeView NodeAt(Vector2 panelPos)
        {
            var picked = panel?.Pick(panelPos);
            while (picked != null && !(picked is NodeView)) picked = picked.parent;
            return picked as NodeView;
        }

        void OnDown(PointerDownEvent evt)
        {
            var target = evt.target as VisualElement;
            // 候補の一覧の中のクリックは、一覧のボタンに任せる
            for (var e = target; e != null; e = e.parent) if (e == popup) return;
            if (evt.button == 1)
            {
                OpenMenu(evt);
                evt.StopPropagation();
                return;
            }
            Focus();
            if (!(target != null && popupFor != null && target == popupFor.OutPort)) HideCandidates();
            var nv = NodeAt(evt.position);
            if (nv != null && target == nv.OutPort)
            {
                drag = Drag.Connect;
                dragNode = nv;
                connectEnd = ToContent(this.WorldToLocal(evt.position));
            }
            else if (nv != null && target == nv.InPort)
            {
                // 入る側の丸を押すと、つなぎを外す
                Disconnect(nv.Node);
                return;
            }
            else if (nv != null)
            {
                Select(nv.Node);
                drag = Drag.Move;
                dragNode = nv;
                dragOrigin = new Vector2(nv.Node.X, nv.Node.Y);
            }
            else
            {
                drag = Drag.Pan;
                dragOrigin = offset;
            }
            dragStart = evt.position;
            this.CapturePointer(evt.pointerId);
            evt.StopPropagation();
        }

        void OnMove(PointerMoveEvent evt)
        {
            if (!this.HasPointerCapture(evt.pointerId)) return;
            var d = (Vector2)evt.position - dragStart;
            switch (drag)
            {
                case Drag.Pan:
                    offset = dragOrigin + d;
                    ApplyTransform();
                    break;
                case Drag.Move:
                    dragNode.Node.X = dragOrigin.x + d.x / zoom;
                    dragNode.Node.Y = dragOrigin.y + d.y / zoom;
                    dragNode.Refresh();
                    edgeLayer.MarkDirtyRepaint();
                    break;
                case Drag.Connect:
                    connectEnd = ToContent(this.WorldToLocal(evt.position));
                    edgeLayer.MarkDirtyRepaint();
                    break;
            }
        }

        void OnUp(PointerUpEvent evt)
        {
            if (!this.HasPointerCapture(evt.pointerId)) return;
            this.ReleasePointer(evt.pointerId);
            if (drag == Drag.Connect && dragNode != null)
            {
                // 動かさずに離した（クリック）なら候補を出す。ドラッグして別のノードの上で離したら、そこにつなぐ
                if (((Vector2)evt.position - dragStart).sqrMagnitude < 9) ShowCandidates(dragNode);
                else
                {
                    var to = NodeAt(evt.position);
                    if (to != null && Doc.Connect(dragNode.Node.Id, to.Node.Id)) Changed?.Invoke();
                }
            }
            else if (drag == Drag.Move) Changed?.Invoke();
            else if (drag == Drag.Pan && ((Vector2)evt.position - dragStart).sqrMagnitude < 9) Select(null);
            drag = Drag.None;
            dragNode = null;
            edgeLayer.MarkDirtyRepaint();
        }

        void OnWheel(WheelEvent evt)
        {
            var local = this.WorldToLocal(evt.mousePosition);
            var before = ToContent(local);
            zoom = Mathf.Clamp(zoom * (evt.delta.y > 0 ? 0.9f : 1.1f), 0.3f, 2f);
            offset = local - before * zoom;
            ApplyTransform();
            evt.StopPropagation();
        }
    }
}
