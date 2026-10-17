using System;
using System.Collections.Generic;
using System.Linq;
using UnityEngine;
using UnityEngine.UIElements;

namespace CardGen.App
{
    /// <summary>ノードを並べてつなぐキャンバス（背景のドラッグで移動、ホイールで拡大縮小）</summary>
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
            }
            edgeLayer.MarkDirtyRepaint();
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
            if (selected == null) return;
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
            Focus();
            var target = evt.target as VisualElement;
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
                var to = NodeAt(evt.position);
                if (to != null && Doc.Connect(dragNode.Node.Id, to.Node.Id)) Changed?.Invoke();
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
