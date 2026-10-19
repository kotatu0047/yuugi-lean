using System.Collections.Generic;
using System.Linq;
using UnityEngine;
using UnityEngine.UIElements;

namespace CardGen.App
{
    /// <summary>
    /// テストプレイのドラッグアンドドロップ：手札のカードを盤面のマス（「何枚でも」のゾーンなら、その行）へドラッグして置く。
    /// カードを置く方法はこれだけ。今置けない手札はつかめない（クリックで選ぶことはできる）
    /// </summary>
    public sealed partial class PlayView
    {
        // ドロップ先（描き直すたびに作り直す）：要素と、置く先のプレイヤー・ゾーン・マス
        readonly List<(VisualElement el, bool p, int zi, int cell)> dropTargets = new List<(VisualElement, bool, int, int)>();
        // 押している手札（まだ動かしていなければクリック、動かしたらドラッグ）
        (bool p, int h, int pointerId, Vector2 start)? press;
        bool dragging;
        VisualElement ghost;
        const float DragThreshold = 6;

        /// <summary>p の手札の h 番目を、今つかめるか（今どこかに置ける手札だけ）</summary>
        public bool CanGrab(bool p, int h) => game != null && h >= 0 && h < state.Get(p).Hand.Count && CanPlaceNow(p, h);

        /// <summary>手札の h 番目を置く動き（選んでいる手札で払うマナを選んでいればそれ、なければ自動の払い方。向きは今の選択）</summary>
        TChoice PlaceFor(bool p, int h, int zi, int cell)
        {
            var c = state.Get(p).Hand[h];
            var pay = selPlayer == p && selHand == h && customPay != null ? customPay
                : TurnInfo.AutoPay(c, PoolOf(p)) ?? new List<string>();
            return p == turn ? TChoice.Place(h, zi, cell, placeUp, pay) : TChoice.Cast(h, zi, cell, placeUp, pay);
        }

        /// <summary>
        /// ドロップ：p の手札の h 番目を、ゾーン zi の cell 番目のマスに置く。つかめない手札や、置けない場所なら何もせず false
        /// （画面のドラッグと、自動テストの両方から呼ぶ）
        /// </summary>
        public bool DropHand(bool p, int h, int zi, int cell)
        {
            if (!CanGrab(p, h)) return false;
            var ch = PlaceFor(p, h, zi, cell);
            if (match.Step(game.Rules, ch) == null)
            {
                log.Add($"（置けません）{state.Get(p).Hand[h].Name} は{CellName(zi, cell)}に置けません");
                Render();
                return false;
            }
            var c = state.Get(p).Hand[h];
            Do(ch, $"{Who(p)}：{c.Name} を{CellName(zi, cell)}に{(placeUp ? "表側" : "裏側")}で置く{PayText(ch.Pay)}" +
                   (p != turn ? "（相手のターンにインスタントとして）" : ""));
            return true;
        }

        /// <summary>空きのマス（や「何枚でも」のゾーンの行）をドロップ先にする</summary>
        void RegisterDrop(VisualElement el, bool p, int zi, int cell) => dropTargets.Add((el, p, zi, cell));

        /// <summary>手札のカードを押したら、PlayView がポインターをつかむ（ボタンのクリックには渡さない）</summary>
        void AttachHandDrag(VisualElement chip, bool p, int h)
        {
            chip.RegisterCallback<PointerDownEvent>(evt =>
            {
                if (evt.button != 0) return;
                press = (p, h, evt.pointerId, evt.position);
                dragging = false;
                this.CapturePointer(evt.pointerId);
                evt.StopImmediatePropagation();
            }, TrickleDown.TrickleDown);
            if (CanGrab(p, h)) chip.tooltip = "ドラッグして盤面のマスに置く";
        }

        void RegisterDragEvents()
        {
            RegisterCallback<PointerMoveEvent>(OnDragMove);
            RegisterCallback<PointerUpEvent>(OnDragUp);
            RegisterCallback<PointerCaptureOutEvent>(_ => { if (press != null) EndDrag(); });
        }

        void OnDragMove(PointerMoveEvent evt)
        {
            if (!(press is (bool p, int h, int id, Vector2 start)) || evt.pointerId != id) return;
            var pos = (Vector2)evt.position;
            if (!dragging)
            {
                if ((pos - start).magnitude < DragThreshold || !CanGrab(p, h)) return;
                dragging = true;
                ShowGhost(state.Get(p).Hand[h]);
            }
            if (ghost != null)
            {
                ghost.style.left = pos.x - 60;
                ghost.style.top = pos.y - 18;
            }
            AutoScroll(pos);
            PaintTargets(p, h, pos);
        }

        void OnDragUp(PointerUpEvent evt)
        {
            if (!(press is (bool p, int h, int id, Vector2 _)) || evt.pointerId != id) return;
            var wasDragging = dragging;
            // 落とした先は、描き直す前の（画面に並んでいる）マスで探す
            var pos = (Vector2)evt.position;
            var t = dropTargets.FirstOrDefault(x => x.p == p && x.el.panel != null && x.el.worldBound.Contains(pos));
            EndDrag();
            if (!wasDragging)
            {
                // 動かさずに離した：クリックとして選ぶ
                SelectHand(p, h);
                return;
            }
            if (t.el == null)
            {
                log.Add($"（置けません）{state.Get(p).Hand[h].Name}：{Who(p)}の側の、置けるマスの上で離してください");
                Render();
                return;
            }
            DropHand(p, h, t.zi, t.cell);
        }

        void EndDrag()
        {
            if (press is (bool _, int _, int id, Vector2 _) && this.HasPointerCapture(id)) this.ReleasePointer(id);
            press = null;
            var was = dragging;
            dragging = false;
            ghost?.RemoveFromHierarchy();
            ghost = null;
            if (was) Render();
        }

        /// <summary>カーソルについてくるカードの影</summary>
        void ShowGhost(Card c)
        {
            var root = panel?.visualTree;
            if (root == null) return;
            ghost = new VisualElement { pickingMode = PickingMode.Ignore };
            ghost.style.position = Position.Absolute;
            ghost.style.width = 120;
            ghost.style.paddingLeft = 8;
            ghost.style.paddingTop = 6;
            ghost.style.paddingBottom = 6;
            ghost.style.opacity = 0.9f;
            Theme.Frame(ghost, Theme.Amber, Theme.Alpha(Theme.Panel, 0.95f), Theme.Amber);
            ghost.Add(Text(c.Name, 12, Theme.Bright, true));
            ghost.Add(Text($"{(placeUp ? "表側" : "裏側")}で置く", 10, Theme.Amber));
            root.Add(ghost);
        }

        /// <summary>置けるマスを緑、置けないマスを暗く。カーソルの下の置けるマスはさらに明るく</summary>
        void PaintTargets(bool p, int h, Vector2 pos)
        {
            foreach (var (el, q, zi, cell) in dropTargets)
            {
                if (el.panel == null) continue;
                var ok = q == p && match.Step(game.Rules, PlaceFor(p, h, zi, cell)) != null;
                var over = ok && el.worldBound.Contains(pos);
                el.style.opacity = ok ? 1f : 0.3f;
                el.style.backgroundColor = ok ? Theme.Alpha(Good, over ? 0.3f : 0.1f) : StyleKeyword.Null;
                if (ok) Theme.Border(el.style, over ? 2 : 1, Theme.Alpha(Good, over ? 1f : 0.7f));
            }
        }

        /// <summary>ドラッグ中に盤面の上下の端へ近づいたら、盤面をスクロールする（自分の手札とマスが同じ画面に入らないとき）</summary>
        void AutoScroll(Vector2 pos)
        {
            var b = boardScroll.worldBound;
            const float edge = 48, speed = 14;
            var y = boardScroll.scrollOffset.y;
            if (pos.y < b.yMin + edge) y -= speed;
            else if (pos.y > b.yMax - edge) y += speed;
            else return;
            boardScroll.scrollOffset = new Vector2(boardScroll.scrollOffset.x, Mathf.Max(0, y));
        }
    }
}
