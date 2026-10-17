using System;
using System.Collections.Generic;
using System.Linq;
using Newtonsoft.Json;
using Newtonsoft.Json.Linq;
using UnityEngine;
using UnityEngine.UIElements;

namespace CardGen.App
{
    /// <summary>
    /// 命題を追加して証明のジョブにする欄と、ジョブの状態の一覧。
    /// 命題は「フィールド上の、条件に合うカードは最大 n 枚」の形（Lean の CustomClaim）。
    /// まず検査ツールが実際に対戦を進めて反例を探し、なければ jobs/pending にジョブを書き出す。
    /// ジョブは開発中は Claude が証明する（この会話で「キューを処理して」）。
    /// </summary>
    public sealed class ClaimPanel : VisualElement
    {
        readonly Func<Game> getGame;
        readonly Func<string> getCommand;
        readonly TextField title = new TextField("文") { value = "自分のフィールド上の闇属性のモンスターは最大5枚" };
        readonly TextField types = new TextField("カードの種類") { value = "モンスター" };
        readonly TextField tags = new TextField("タグ（すべて持つ）") { value = "闇属性" };
        readonly Toggle both = new Toggle("両プレイヤーの合計") { value = false };
        readonly IntegerField n = new IntegerField("最大枚数") { value = 5 };
        readonly Label message = new Label();
        readonly VisualElement jobs = new VisualElement();
        bool busy;

        static readonly Color Good = new Color(0.45f, 0.8f, 0.5f);
        static readonly Color Bad = new Color(0.95f, 0.45f, 0.4f);
        static readonly Color Quiet = new Color(0.7f, 0.7f, 0.75f);

        public ClaimPanel(Func<Game> getGame, Func<string> getCommand)
        {
            this.getGame = getGame;
            this.getCommand = getCommand;
            style.paddingLeft = 12;
            style.paddingRight = 12;
            style.paddingBottom = 16;
            style.borderTopWidth = 1;
            style.borderTopColor = new Color(0.3f, 0.3f, 0.33f);

            var head = new Label("命題とジョブ");
            head.style.fontSize = 14;
            head.style.unityFontStyleAndWeight = FontStyle.Bold;
            head.style.color = Color.white;
            head.style.marginTop = 10;
            Add(head);
            var hint = new Label("「フィールド上の、条件に合うカードは最大 n 枚」を追加できます。反例がなければ証明のジョブになり、" +
                                 "開発中は Claude が証明します（「キューを処理して」と頼む）。");
            hint.style.whiteSpace = WhiteSpace.Normal;
            hint.style.fontSize = 11;
            hint.style.color = Quiet;
            Add(hint);
            Add(title);
            Add(types);
            Add(tags);
            Add(both);
            Add(n);
            var row = new VisualElement();
            row.style.flexDirection = FlexDirection.Row;
            row.Add(new Button(() => _ = Submit()) { text = "反例を探してジョブにする" });
            row.Add(new Button(() => _ = Refresh()) { text = "ジョブの状態を更新" });
            Add(row);
            message.style.whiteSpace = WhiteSpace.Normal;
            message.style.fontSize = 12;
            message.style.marginTop = 4;
            Add(message);
            Add(jobs);
        }

        static List<string> Split(string s) =>
            s.Split(new[] { ',', '、', '・', '，' }, StringSplitOptions.RemoveEmptyEntries).Select(x => x.Trim()).Where(x => x.Length > 0).ToList();

        void Say(string s, Color c) { message.text = s; message.style.color = c; }

        public async System.Threading.Tasks.Task Submit()
        {
            if (busy) return;
            busy = true;
            Say("反例を探しています…", Quiet);
            try
            {
                var claim = new JObject
                {
                    ["title"] = title.value,
                    ["types"] = new JArray(Split(types.value)),
                    ["tags"] = new JArray(Split(tags.value)),
                    ["both"] = both.value,
                    ["n"] = Math.Max(0, n.value),
                };
                var input = new JObject { ["game"] = IrJson.ToJson(getGame()), ["claim"] = claim };
                var output = await CheckerClient.Run(CheckerClient.WithArgs(getCommand(), "--job-stdin"), input.ToString(Formatting.None));
                var o = JObject.Parse(output);
                switch ((string)o["status"])
                {
                    case "queued":
                        Say($"反例は見つかりませんでした。ジョブ {(string)o["id"]} として証明待ちにしました。", Good);
                        break;
                    case "counterexample":
                        var moves = ((JArray)o["choices"]).Count;
                        Say($"反例があります：条件に合うデッキで {moves} 手進めると、条件に合うカードが {(int)o["count"]} 枚になります（最大 {n.value} 枚を超える）。", Bad);
                        break;
                    default:
                        Say("形式の誤りがあります：" + string.Join("、", o["errors"]?.Select(x => (string)x) ?? new string[0]), Bad);
                        break;
                }
                await Refresh();
            }
            catch (Exception e) { Say($"検査ツールを動かせません：{e.Message}", Bad); }
            busy = false;
        }

        public async System.Threading.Tasks.Task Refresh()
        {
            try
            {
                var output = await CheckerClient.Run(CheckerClient.WithArgs(getCommand(), "--jobs"), "");
                jobs.Clear();
                var list = JArray.Parse(output);
                if (list.Count == 0) jobs.Add(new Label("ジョブはまだありません") { style = { color = Quiet, fontSize = 11 } });
                foreach (var j in list)
                {
                    var st = (string)j["status"];
                    var label = st == "accepted" ? "証明済み" : st == "rejected" ? "差し戻し" : "証明待ち";
                    var l = new Label($"{(string)j["id"]}　[{label}]　{(string)j["title"]}");
                    l.style.whiteSpace = WhiteSpace.Normal;
                    l.style.fontSize = 11;
                    l.style.marginTop = 2;
                    l.style.color = st == "accepted" ? Good : st == "rejected" ? Bad : Quiet;
                    jobs.Add(l);
                }
            }
            catch (Exception e) { Say($"ジョブの一覧を読めません：{e.Message}", Bad); }
        }
    }
}
