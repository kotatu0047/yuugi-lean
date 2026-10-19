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

        /// <summary>p の手札の i 番目の右クリックのメニュー：そのカードを選び、右の欄と同じ動きを出す</summary>
        public List<MenuEntry> HandMenu(bool p, int i)
        {
            SelectHand(p, i);
            var c = state.Get(p).Hand[i];
            var items = new List<MenuEntry> { MenuEntry.Header($"{Who(p)}の手札：{c.Name}（{c.Type}）") };
            items.AddRange(SelectionItems());
            if (selectionActions.Any(a => a.Text.Contains("で置く")))
            {
                items.Add(MenuEntry.Separator());
                items.Add(MenuEntry.Item($"置く向きを{(placeUp ? "裏側" : "表側")}にする", () => { placeUp = !placeUp; Render(); }));
            }
            return items;
        }

        /// <summary>p のフィールドの i 番目の右クリックのメニュー：そのカードを選び、右の欄と同じ動きを出す</summary>
        public List<MenuEntry> FieldMenu(bool p, int i)
        {
            SelectField(p, i);
            var sl = state.Get(p).Field[i];
            var items = new List<MenuEntry> { MenuEntry.Header($"{Who(p)}のフィールド：{sl.Card.Name}" + (sl.FaceUp ? "" : "（裏側）")) };
            items.AddRange(SelectionItems());
            return items;
        }

        List<MenuEntry> SelectionItems() =>
            selectionActions.Count > 0 ? selectionActions.ToList()
            : new List<MenuEntry> { MenuEntry.Item("今このカードでできる動きはありません（理由は右の欄）", null, false) };

        /// <summary>盤面・右の欄の空き場所の右クリックのメニュー：今できる動き（対象・スタック・ブロックなど）と、対戦の操作</summary>
        public List<MenuEntry> GeneralMenu()
        {
            var items = new List<MenuEntry>();
            if (game == null) return items;
            if (panelActions.Count > 0)
            {
                items.Add(MenuEntry.Header("今できること"));
                items.AddRange(panelActions);
                items.Add(MenuEntry.Separator());
            }
            var t = match.Turn;
            items.Add(MenuEntry.Header($"第{turnCount}ターン：{Who(turn)}のターン・優先権：{Who(t.Prio)}"));
            if (t.Passes < 2 && !match.Over(game.Rules))
                items.Add(MenuEntry.Item($"{Who(t.Prio)}がパスする", () => Do(TChoice.Pass(), $"{Who(match.Turn.Prio)}：パス")));
            items.Add(MenuEntry.Item("ターン終了", () => { EndTurn(); Render(); }, CanEndTurn));
            items.Add(MenuEntry.Separator());
            items.Add(MenuEntry.Item("最初から（混ぜ直す）", () => { seed++; Start(game); }));
            items.Add(MenuEntry.Item($"{Who(!firstPlayer)}の先攻で最初から", () => { firstPlayer = !firstPlayer; Start(game); }));
            items.Add(MenuEntry.Item("記録をコピーする", () => GUIUtility.systemCopyBuffer = string.Join("\n", log)));
            if (Exit != null) items.Add(MenuEntry.Item("エディタに戻る", Exit));
            return items;
        }
    }
}
