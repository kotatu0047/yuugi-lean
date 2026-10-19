using System;
using System.Collections.Generic;
using System.Linq;
using UnityEngine;
using UnityEngine.UIElements;

namespace CardGen.App
{
    /// <summary>
    /// ノードを並べてつなぐキャンバス（背景のドラッグで移動、ホイールで拡大縮小）。
    /// ノードの右の丸にカーソルを合わせる（またはクリックする）と、つなげるノードの候補が出て、選ぶとつないだ状態で加わる
    /// </summary>
    public sealed class GraphCanvas : VisualElement
    {
        public GraphDoc Doc { get; private set; } = new GraphDoc();
        public event Action<Node> Selected;
        public event System.Action Changed;

        readonly VisualElement content;
        readonly VisualElement edgeLayer;
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
            style.backgroundColor = new Color(0.11f, 0.11f, 0.12f);
            focusable = true;

            content = new VisualElement { name = "content", pickingMode = PickingMode.Ignore };
            content.style.position = Position.Absolute;
            content.style.left = 0;
            content.style.top = 0;
            content.style.width = 4000;
            content.style.height = 4000;
            content.style.transformOrigin = new TransformOrigin(0, 0);
            Add(content);

            edgeLayer = new VisualElement { name = "edges", pickingMode = PickingMode.Ignore };
            edgeLayer.style.position = Position.Absolute;
            edgeLayer.style.left = 0;
            edgeLayer.style.top = 0;
            edgeLayer.style.width = 4000;
            edgeLayer.style.height = 4000;
            edgeLayer.generateVisualContent += DrawEdges;
            content.Add(edgeLayer);

            popup = new VisualElement { name = "candidates" };
            popup.style.position = Position.Absolute;
            popup.style.display = DisplayStyle.None;
            popup.style.backgroundColor = new Color(0.16f, 0.16f, 0.19f, 0.98f);
            popup.style.borderTopLeftRadius = popup.style.borderTopRightRadius =
                popup.style.borderBottomLeftRadius = popup.style.borderBottomRightRadius = 6;
            popup.style.borderLeftWidth = popup.style.borderRightWidth = popup.style.borderTopWidth = popup.style.borderBottomWidth = 1;
            popup.style.borderLeftColor = popup.style.borderRightColor = popup.style.borderTopColor = popup.style.borderBottomColor =
                new Color(1f, 0.85f, 0.3f, 0.7f);
            popup.style.paddingLeft = popup.style.paddingRight = 6;
            popup.style.paddingTop = popup.style.paddingBottom = 6;
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
            var head = new Label($"{v.Node.Title} につなぐ") { style = { fontSize = 11, color = new Color(0.8f, 0.8f, 0.85f), marginBottom = 4 } };
            popup.Add(head);
            foreach (var k in GraphDoc.Candidates(v.Node.Kind))
            {
                var kind = k;
                var b = new Button(() => AddCandidate(kind)) { text = Node.KindLabel(kind) };
                b.style.marginLeft = b.style.marginRight = 0;
                b.style.marginTop = b.style.marginBottom = 1;
                b.style.unityTextAlign = TextAnchor.MiddleLeft;
                b.style.borderLeftWidth = 4;
                b.style.borderLeftColor = NodeView.KindColor(kind);
                popup.Add(b);
            }
            if (Node.TakesSelector(v.Node.Kind) && Doc.Children(v.Node).Count > 0)
                popup.Add(new Label("（今の範囲と入れ替わります）") { style = { fontSize = 10, color = new Color(0.65f, 0.65f, 0.7f) } });
            var port = v.OutPort.worldBound;
            var local = this.WorldToLocal(new Vector2(port.xMax + 6, port.yMin - 4));
            popup.style.left = Mathf.Min(local.x, Mathf.Max(0, layout.width - 200));
            popup.style.top = Mathf.Max(0, local.y);
            popup.style.display = DisplayStyle.Flex;
            popup.BringToFront();
        }

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
            if (popupFor == null) return;
            var parent = popupFor.Node;
            var n = Doc.AddChild(parent, kind, x => views.TryGetValue(x.Id, out var nv) ? HeightOf(nv) : 100, WidthOf(popupFor));
            Rebuild();
            Select(n);
            Changed?.Invoke();
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

        void DrawCurve(Painter2D p, Vector2 a, Vector2 b, Color c)
        {
            float dx = Mathf.Max(40, Mathf.Abs(b.x - a.x) * 0.5f);
            p.strokeColor = c;
            p.lineWidth = 2.5f;
            p.BeginPath();
            p.MoveTo(a);
            p.BezierCurveTo(a + new Vector2(dx, 0), b - new Vector2(dx, 0), b);
            p.Stroke();
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
                DrawCurve(p, OutPos(dragNode.Node), connectEnd, new Color(1f, 0.85f, 0.3f));
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
                Doc.Edges.RemoveAll(e => e.To == nv.Node.Id);
                edgeLayer.MarkDirtyRepaint();
                Changed?.Invoke();
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
