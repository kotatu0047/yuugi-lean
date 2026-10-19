using System.Collections.Generic;
using System.Linq;
using UnityEngine.UIElements;

namespace CardGen.App
{
    /// <summary>
    /// 画面の自動テスト用の小道具。ボタンは押したときの処理を覚えておき（userData）、テストから文字で探して押せるようにする
    /// （パネルに載っていない要素にはクリックのイベントが届かないため）
    /// </summary>
    public static class UiTest
    {
        /// <summary>押したときの処理を覚えたボタン</summary>
        public static Button Btn(string text, System.Action action)
        {
            var b = new Button(action) { text = text };
            b.userData = action;
            return b;
        }

        /// <summary>root の中の、押せるボタンの文字</summary>
        public static List<string> Buttons(VisualElement root) =>
            root.Query<Button>().ToList().Where(b => b.enabledSelf && b.userData is System.Action).Select(b => b.text).ToList();

        /// <summary>root の中の、文字に text を含む押せるボタンを押す（なければ false）</summary>
        public static bool Press(VisualElement root, string text)
        {
            var b = root.Query<Button>().ToList()
                .FirstOrDefault(x => x.enabledSelf && x.userData is System.Action && x.text.Contains(text));
            if (b == null) return false;
            ((System.Action)b.userData)();
            return true;
        }
    }
}
