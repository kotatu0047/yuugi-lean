using System.Collections.Generic;
using System.Linq;
using UnityEngine;

namespace CardGen.App
{
    /// <summary>テストプレイの右クリックのメニュー（カードの上と、盤面・右の欄の空き場所）</summary>
    public sealed partial class PlayView
    {
        /// <summary>ターンを終えられるか（攻撃の途中でもスタックがあるのでもなく、ターンプレイヤーが優先権を持つ）</summary>
        bool CanEndTurn => match.Turn.Quiet && !match.Over(game.Rules) && match.Turn.Prio == turn && match.Turn.Passes < 2;

        /// <summary>ターンを終えられない理由（終えられるなら null）</summary>
        string EndTurnBlocked()
        {
            var t = match.Turn;
            if (match.Over(game.Rules)) return "対戦は終わっています";
            if (t.Stack.Count > 0) return "スタックにカードがあります（解決してから）";
            if (t.Attackers.Count > 0) return "攻撃の途中です（ブロックを選んでから）";
            if (t.Prio != turn) return $"優先権が{Who(t.Prio)}にあります（{Who(t.Prio)}がパスしてから）";
            if (t.Passes >= 2) return "両者がパスした直後です";
            return null;
        }

        /// <summary>p の手札の i 番目の右クリックのメニュー：そのカードを選び、右の欄と同じ動きを出す</summary>
        public List<MenuEntry> HandMenu(bool p, int i)
        {
            SelectHand(p, i);
            var c = state.Get(p).Hand[i];
            var items = new List<MenuEntry>
            {
                MenuEntry.Title(c.Name, $"{Who(p)}の手札・{c.Type}" + (UsesMana ? $"・コスト {CostText(c)}" : ""), NodeView.KindColor(NodeKind.Card)),
            };
            items.AddRange(SelectionItems());
            if (selectionActions.Any(a => a.Text.Contains("で置く")))
            {
                items.Add(MenuEntry.Separator());
                items.Add(MenuEntry.Item($"置く向きを{(placeUp ? "裏側" : "表側")}にする", () => { placeUp = !placeUp; Render(); },
                    hint: $"今は{(placeUp ? "表側" : "裏側")}で置きます"));
            }
            return items;
        }

        /// <summary>p のフィールドの i 番目の右クリックのメニュー：そのカードを選び、右の欄と同じ動きを出す</summary>
        public List<MenuEntry> FieldMenu(bool p, int i)
        {
            SelectField(p, i);
            var sl = state.Get(p).Field[i];
            var items = new List<MenuEntry>
            {
                MenuEntry.Title(sl.Card.Name, $"{Who(p)}のフィールド・{sl.Card.Type}" + (sl.FaceUp ? "" : "・裏側") +
                    (TappedAt(p, i) ? "・タップ中" : ""), NodeView.KindColor(NodeKind.Card)),
            };
            items.AddRange(SelectionItems());
            return items;
        }

        List<MenuEntry> SelectionItems()
        {
            var items = new List<MenuEntry> { MenuEntry.Header("できる動き") };
            if (selectionActions.Count > 0) items.AddRange(selectionActions);
            else items.Add(MenuEntry.Item("今このカードでできる動きはありません", null, false, "理由は右の欄に出ています"));
            return items;
        }

        /// <summary>盤面・右の欄の空き場所の右クリックのメニュー：今できる動き（対象・スタック・ブロックなど）と、対戦の操作</summary>
        public List<MenuEntry> GeneralMenu()
        {
            var items = new List<MenuEntry>();
            if (game == null) return items;
            var t = match.Turn;
            items.Add(MenuEntry.Title($"第{turnCount}ターン：{Who(turn)}のターン", $"優先権：{Who(t.Prio)}" +
                (t.Stack.Count > 0 ? $"・スタック {t.Stack.Count} 枚" : "") + (t.Attackers.Count > 0 ? "・攻撃の途中" : "")));
            if (panelActions.Count > 0)
            {
                items.Add(MenuEntry.Header("今できること"));
                items.AddRange(panelActions);
                items.Add(MenuEntry.Separator());
            }
            items.Add(MenuEntry.Header("対戦"));
            if (t.Passes < 2 && !match.Over(game.Rules))
                items.Add(MenuEntry.Item($"{Who(t.Prio)}がパスする", () => Do(TChoice.Pass(), $"{Who(match.Turn.Prio)}：パス"),
                    hint: $"優先権が{Who(!t.Prio)}に移ります"));
            var blocked = EndTurnBlocked();
            items.Add(MenuEntry.Item("ターン終了", () => { EndTurn(); Render(); }, blocked == null,
                blocked ?? $"{Who(!turn)}のターンになり、{Who(!turn)}が引きます"));
            items.Add(MenuEntry.Separator());
            items.Add(MenuEntry.Header("やり直す・ほか"));
            items.Add(MenuEntry.Item("最初から", () => { seed++; Start(game); }, hint: "山札を混ぜ直します"));
            items.Add(MenuEntry.Item($"{Who(!firstPlayer)}の先攻で最初から", () => { firstPlayer = !firstPlayer; Start(game); }));
            items.Add(MenuEntry.Item("記録をコピーする", () => GUIUtility.systemCopyBuffer = string.Join("\n", log), hint: "クリップボードへ"));
            if (Exit != null) items.Add(MenuEntry.Item("エディタに戻る", Exit));
            return items;
        }
    }
}
