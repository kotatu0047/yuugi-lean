using System;
using System.Collections.Generic;
using System.Linq;
using UnityEngine;
using UnityEngine.UIElements;

namespace CardGen.App
{
    /// <summary>テストプレイの盤面の表示（カード・マス・盤面のマス目）</summary>
    public sealed partial class PlayView
    {

        static Label Text(string s, int size = 12, Color? color = null, bool bold = false)
        {
            var l = new Label(s);
            l.style.whiteSpace = WhiteSpace.Normal;
            l.style.fontSize = Mathf.Max(size, 11); // 読めるように 11 より小さくはしない
            if (color.HasValue) l.style.color = color.Value;
            if (bold) l.style.unityFontStyleAndWeight = FontStyle.Bold;
            return l;
        }

        static VisualElement Row()
        {
            var r = new VisualElement();
            r.style.flexDirection = FlexDirection.Row;
            r.style.flexWrap = Wrap.Wrap;
            r.style.alignItems = Align.FlexStart;
            return r;
        }

        VisualElement Chip(Card c, bool faceUp, string status, bool selected, System.Action onClick, string stats = null,
                           Func<List<MenuEntry>> menu = null)
        {
            var b = UiTest.Btn("", onClick);
            if (menu != null) PopupMenu.Attach(b, _ => menu());
            b.style.width = 120;
            b.style.flexShrink = 0;
            b.style.minHeight = CellHeight;
            b.style.marginRight = 6;
            b.style.marginBottom = 6;
            b.style.flexDirection = FlexDirection.Column;
            b.style.alignItems = Align.FlexStart;
            b.style.paddingLeft = 6;
            b.style.paddingTop = 4;
            // HUD のカード：表側はアンバー、裏側は紫の、透ける地と細い枠。選んでいれば枠と四隅のブラケットを明るく
            var color = faceUp ? Theme.Amber : Theme.Kind(NodeKind.Counter);
            b.style.backgroundColor = Theme.Alpha(color, selected ? 0.16f : 0.06f);
            Theme.Border(b.style, 1, selected ? Theme.Amber : Theme.Alpha(color, 0.45f));
            Theme.Round(b.style, 1);
            Theme.Brackets(b, () => selected ? Theme.Amber : Theme.Alpha(color, 0.8f), selected ? 10 : 6, selected ? 2f : 1.2f);
            b.Add(Text(c.Name, 11, Theme.Bright, true));
            b.Add(Text(c.Type + (faceUp ? "" : "・裏側"), 12, Quiet));
            if (stats != null) b.Add(Text(stats, 10, Theme.Alpha(Theme.Amber, 0.9f)));
            if (status != null)
                b.Add(Text(status, 10, status == "有効" || status == "置ける" ? Good : status == "無効" ? Bad : Warn, true));
            return b;
        }

        VisualElement PlayerBoard(bool p, Dictionary<(bool, int), string> neg)
        {
            var s = state.Get(p);
            var box = new VisualElement();
            box.style.marginBottom = 12;
            box.style.paddingLeft = 10;
            box.style.paddingRight = 10;
            box.style.paddingTop = 8;
            box.style.paddingBottom = 4;
            Theme.Frame(box, p == turn ? Theme.LineHi : Theme.Line, Theme.Panel, p == turn ? Theme.Amber : Theme.Alpha(Theme.Cyan, 0.6f));
            // プレイヤーの盤面の空き場所の右クリック：ライフ・デッキ・手札・墓地
            PopupMenu.Attach(box, _ => PlayerMenu(p));

            var head = Row();
            head.style.alignItems = Align.Center;
            var unit = Theme.Tag(p ? "unit // self" : "unit // opponent", p == turn ? Theme.Amber : Theme.Muted, 9);
            unit.style.marginRight = 8;
            head.Add(unit);
            head.Add(Text(Who(p), 15, Theme.Bright, true));
            if (p == turn) head.Add(Text("　ターン中", 12, Warn, true));
            if (game.Rules.Life > 0)
                head.Add(Text($"　ライフ {s.Life}", 15, s.Life == 0 ? Bad : Good, true));
            head.Add(Text($"　デッキ {s.Deck.Count} 枚・墓地 {s.Grave.Count} 枚", 12, Quiet));
            if (p == turn)
            {
                var end = UiTest.Btn("ターン終了", () => { EndTurn(); Render(); });
                end.style.marginLeft = 12;
                end.SetEnabled(CanEndTurn);
                head.Add(end);
            }
            box.Add(head);

            var zones = new VisualElement();
            // 相手のフィールドは自分のフィールドを逆さまにした形（共通ルール②）なので、ゾーンの並びも逆にする。
            // マスの位置があるゾーンは、真ん中のマス目の表示（GridBoard）に出す
            var order = Enumerable.Range(0, game.Rules.Zones.Count).ToList();
            if (!p) order.Reverse();
            foreach (var zi in order)
            {
                var z = game.Rules.Zones[zi];
                if (z.Role != ZoneRole.Plain || z.Cells.Count > 0) continue;
                var zr = Row();
                zr.style.alignItems = Align.Center;
                zr.style.marginTop = 6;
                var title = Text($"{z.Name}（{z.Count}マス）", 11, NodeView.KindColor(NodeKind.Zone), true);
                title.style.width = 170;
                zr.Add(title);
                if (z.Capacity == Capacity.One)
                {
                    var cells = Enumerable.Range(0, z.Count).ToList();
                    if (!p) cells.Reverse();
                    foreach (var k in cells) zr.Add(CellView(p, zi, k, neg));
                }
                else
                {
                    foreach (var (sl, i) in s.Field.Select((sl, i) => (sl, i)).Where(x => x.sl.Zone == zi))
                        zr.Add(SlotChip(p, i, sl, neg));
                    // 「何枚でも」のゾーンは、行全体がドロップ先
                    RegisterDrop(zr, p, zi, 0);
                    if (CanPlaceSelected(p, zi, 0)) zr.Add(Text("← ここへドラッグして置ける", 10, Good));
                }
                zones.Add(zr);
            }

            var hand = Row();
            hand.style.marginTop = 8;
            var ht = Text("手札", 12, Quiet, true);
            ht.style.width = 170;
            hand.Add(ht);
            for (int i = 0; i < s.Hand.Count; i++)
            {
                int idx = i;
                var hc = s.Hand[i];
                var hchip = Chip(hc, true, CanPlaceNow(p, idx) ? "置ける（ドラッグ）" : null, selPlayer == p && selHand == idx, () => { selPlayer = p; selHand = idx; selField = -1; customPay = null; Render(); },
                    UsesMana ? (hc.Mana > 0 ? ManaText(hc) : $"コスト {CostText(hc)}") : null, () => HandMenu(p, idx));
                AttachHandDrag(hchip, p, idx);
                hand.Add(hchip);
            }

            // 相手のフィールドは自分のフィールドを逆さまにした形（共通ルール②）
            if (p) { box.Add(zones); box.Add(hand); }
            else { box.Add(hand); box.Add(zones); }
            return box;
        }

        /// <summary>フィールドのカード1枚の表示（クリックで選ぶ）</summary>
        VisualElement SlotChip(bool p, int i, Slot sl, Dictionary<(bool, int), string> neg)
        {
            neg.TryGetValue((p, i), out var st);
            string stats = null;
            if (MatchState.Fights(game.Rules, sl))
            {
                var atk = state.AtkOf(game.Rules, NegList(neg), (p, i), sl);
                var def = state.DefOf(game.Rules, NegList(neg), (p, i), sl);
                stats = $"攻 {atk}" + (atk != sl.Card.Attack ? $"（元 {sl.Card.Attack}）" : "") +
                        $"・守 {def}" + (def != sl.Card.Defense ? $"（元 {sl.Card.Defense}）" : "");
                if (sl.Card.Trample) stats += "・トランプル";
                if (sl.Card.Flying) stats += "・飛行";
                if (sl.Card.Reach) stats += "・到達";
                if (sl.Damage > 0) stats += $"\nダメージ {sl.Damage}（残り {Math.Max(0, def - sl.Damage)}）";
            }
            var f = state.Get(p).Field;
            var tapped = UsesMana && TappedAt(p, i);
            if (UsesMana)
            {
                var notes = new List<string>();
                if (tapped) notes.Add("タップ中");
                if (sl.Card.Mana > 0) notes.Add(ManaText(sl.Card));
                if (p == turn && match.Turn.Sick(game.Rules, f, sl)) notes.Add("召喚酔い");
                if (notes.Count > 0) stats = (stats == null ? "" : stats + "\n") + string.Join("・", notes);
            }
            var chip = Chip(sl.Card, sl.FaceUp, st, selPlayer == p && selField == i,
                () => { selPlayer = p; selField = i; selHand = -1; customPay = null; Render(); }, stats, () => FieldMenu(p, i));
            if (tapped) chip.style.opacity = 0.75f;
            return chip;
        }

        /// <summary>
        /// p のフィールドの i 番目のカードをタップしている状態で表示するか。記録は「同じカードのうち何枚がタップしているか」
        /// だけなので（Lean のモデルと同じ）、同じカードが複数あれば前から順にその枚数をタップしている状態で表示する
        /// </summary>
        bool TappedAt(bool p, int i)
        {
            var f = state.Get(p).Field;
            var sl = f[i];
            var rec = p == turn ? match.Turn.Tapped : match.Turn.OppTapped;
            var before = f.Take(i + 1).Count(x => TurnInfo.SameSlot(x, sl));
            return before <= rec.Count(x => TurnInfo.SameSlot(x, sl));
        }

        /// <summary>p の手札の h 番目を、今どこかに置けるか（自動の払い方で）</summary>
        bool CanPlaceNow(bool p, int h)
        {
            var c = state.Get(p).Hand[h];
            var pay = TurnInfo.AutoPay(c, PoolOf(p));
            if (pay == null) return false;
            for (int zi = 0; zi < game.Rules.Zones.Count; zi++)
            {
                var cell = state.FreeCell(game.Rules, p, zi);
                var ch = p == turn ? TChoice.Place(h, zi, cell, true, pay) : TChoice.Cast(h, zi, cell, true, pay);
                if (match.Step(game.Rules, ch) != null) return true;
            }
            return false;
        }

        /// <summary>空きのマス</summary>
        VisualElement EmptyCell(string label)
        {
            var empty = new VisualElement();
            empty.style.width = 120;
            empty.style.flexShrink = 0;
            empty.style.height = CellHeight;
            empty.style.marginRight = 6;
            empty.style.marginBottom = 6;
            empty.style.borderLeftWidth = empty.style.borderRightWidth = empty.style.borderTopWidth = empty.style.borderBottomWidth = 1;
            empty.style.borderLeftColor = empty.style.borderRightColor = empty.style.borderTopColor = empty.style.borderBottomColor = Line;
            if (label != null)
            {
                var l = Text(label, 11, Quiet);
                l.style.paddingLeft = 4;
                l.style.paddingTop = 2;
                empty.Add(l);
            }
            return empty;
        }

        /// <summary>p のゾーン zi の k 番目のマス：カードがあれば表示、空いていれば（置けるなら）置くボタン</summary>
        VisualElement CellView(bool p, int zi, int k, Dictionary<(bool, int), string> neg, string emptyLabel = null)
        {
            var f = state.Get(p).Field;
            var i = f.FindIndex(sl => sl.Zone == zi && sl.Cell == k);
            if (i >= 0) return SlotChip(p, i, f[i], neg);
            // 空きのマスはドロップ先。選んでいる手札を置けるマスは緑の枠で示す。右クリック：そこに置ける手札
            var cell = EmptyCell(emptyLabel);
            if (CanPlaceSelected(p, zi, k))
            {
                Theme.Border(cell.style, 1, Theme.Alpha(Good, 0.7f));
                var hint = Text("ドラッグして置ける", 10, Good);
                hint.style.paddingLeft = 4;
                cell.Add(hint);
            }
            RegisterDrop(cell, p, zi, k);
            PopupMenu.Attach(cell, _ => CellMenu(p, zi, k));
            return cell;
        }

        /// <summary>マスの位置があるゾーンを、盤面のマス目の並びで表示する（行の小さい方が上。見本では相手が上）</summary>
        VisualElement GridBoard(Dictionary<(bool, int), string> neg)
        {
            var at = new Dictionary<Cell, (bool p, int zi, int k)>();
            foreach (var p in new[] { false, true })
                for (int zi = 0; zi < game.Rules.Zones.Count; zi++)
                {
                    var z = game.Rules.Zones[zi];
                    if (z.Role != ZoneRole.Plain) continue;
                    for (int k = 0; k < z.Cells.Count; k++)
                    {
                        var c = game.Rules.CellOf(p, zi, k);
                        if (c.HasValue && !at.ContainsKey(c.Value)) at[c.Value] = (p, zi, k);
                    }
                }
            var box = new VisualElement();
            if (at.Count == 0) return box;
            box.style.marginBottom = 12;
            box.style.paddingLeft = 10;
            box.style.paddingTop = 8;
            box.style.paddingBottom = 4;
            box.style.paddingRight = 10;
            Theme.Frame(box, Theme.Line, Theme.Alpha(Theme.Panel, 0.7f));
            int c0 = at.Keys.Min(c => c.Col), c1 = at.Keys.Max(c => c.Col);
            int r0 = at.Keys.Min(c => c.Row), r1 = at.Keys.Max(c => c.Row);
            var head = Row();
            head.style.alignItems = Align.Center;
            var grid = Theme.Tag("tactical grid", Theme.Cyan, 9);
            grid.style.marginRight = 8;
            head.Add(grid);
            head.Add(Text($"フィールド（盤面のマス目の列 {c0}〜{c1}・行 {r0}〜{r1}。上が相手、下が自分）", 12, Quiet));
            box.Add(head);
            for (int r = r0; r <= r1; r++)
            {
                if (!at.Keys.Any(c => c.Row == r))
                {
                    // マスのない行（見本では盤面の中心の行）は細い区切りにする
                    var sep = Text($"行 {r}（マスなし）", 11, Quiet);
                    sep.style.marginTop = 2;
                    sep.style.marginBottom = 8;
                    sep.style.borderBottomWidth = 1;
                    sep.style.borderBottomColor = Line;
                    box.Add(sep);
                    continue;
                }
                var line = Row();
                line.style.flexWrap = Wrap.NoWrap;
                line.style.alignItems = Align.Center;
                var rowLabel = Text($"行 {r}", 12, Quiet);
                rowLabel.style.width = 40;
                line.Add(rowLabel);
                for (int c = c0; c <= c1; c++)
                {
                    if (!at.TryGetValue(new Cell(c, r), out var x))
                    {
                        var gap = new VisualElement();
                        gap.style.flexShrink = 0;
                        gap.style.width = 126;
                        gap.style.height = CellHeight;
                        line.Add(gap);
                        continue;
                    }
                    line.Add(CellView(x.p, x.zi, x.k, neg, $"{Who(x.p)}の{game.Rules.Zones[x.zi].Name} {x.k + 1}"));
                }
                box.Add(line);
            }
            return box;
        }
    }
}
