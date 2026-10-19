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
    /// 命題は「（フィールド上・手札・墓地・デッキ）の、条件に合うカードは最大 n 枚」の形（Lean の CustomClaim）。
    /// まず検査ツールが実際に対戦を進めて反例を探し、なければ jobs/pending にジョブを書き出す。
    /// ジョブは開発中は Claude が証明する（この会話で「キューを処理して」）。
    /// </summary>
    public sealed class ClaimPanel : VisualElement
    {
        readonly Func<Game> getGame;
        readonly Func<string> getCommand;
        readonly TextField title = new TextField("文") { value = "自分のフィールド上の闇属性のモンスターは最大5枚" };
        // カードの種類とタグは、集合のノードの値から選ぶ
        readonly List<string> types = new List<string> { "モンスター" };
        readonly List<string> tags = new List<string> { "闇属性" };
        readonly VisualElement typeRow = new VisualElement();
        readonly VisualElement tagRow = new VisualElement();
        static readonly (string, string)[] Places = { ("フィールド上", "field"), ("手札", "hand"), ("墓地", "grave"), ("デッキ", "deck") };
        readonly DropdownField place = new DropdownField("数える場所", Places.Select(p => p.Item1).ToList(), 0);
        readonly Toggle both = new Toggle("両プレイヤーの合計") { value = false };
        readonly IntegerField n = new IntegerField("最大枚数") { value = 5 };
        readonly Label message = new Label();
        readonly VisualElement jobs = new VisualElement();
        bool busy;

        static readonly Color Good = Theme.Green;
        static readonly Color Bad = Theme.Red;
        static readonly Color Quiet = Theme.Muted;

        public ClaimPanel(Func<Game> getGame, Func<string> getCommand)
        {
            this.getGame = getGame;
            this.getCommand = getCommand;
            style.paddingLeft = 12;
            style.paddingRight = 12;
            style.paddingBottom = 16;
            style.borderTopWidth = 1;
            style.borderTopColor = Theme.Line;

            Add(Theme.Heading("命題とジョブ", "claim // jobs"));
            var hint = new Label("「（フィールド上・手札・墓地・デッキ）の、条件に合うカードは最大 n 枚」を追加できます。反例がなければ証明のジョブになり、" +
                                 "開発中は Claude が証明します（「キューを処理して」と頼む）。");
            hint.style.whiteSpace = WhiteSpace.Normal;
            hint.style.fontSize = 12;
            hint.style.color = Quiet;
            Add(hint);
            Add(title);
            Add(place);
            Add(typeRow);
            Add(tagRow);
            Add(both);
            Add(n);
            var row = new VisualElement();
            row.style.flexDirection = FlexDirection.Row;
            row.Add(UiTest.Btn("反例を探してジョブにする", () => _ = Submit()));
            row.Add(UiTest.Btn("ジョブの状態を更新", () => _ = Refresh()));
            Add(row);
            message.style.whiteSpace = WhiteSpace.Normal;
            message.style.fontSize = 12;
            message.style.marginTop = 4;
            Add(message);
            Add(jobs);
            SyncChoices();
            PopupMenu.Attach(this, _ => Menu());
        }

        /// <summary>右クリックのメニュー：反例を探す・ジョブの状態を更新・タグの選択を外す</summary>
        public List<MenuEntry> Menu() => new List<MenuEntry>
        {
            MenuEntry.Title("命題とジョブ", title.value),
            MenuEntry.Item("反例を探してジョブにする", () => _ = Submit(), !busy, busy ? "実行しています…" : "反例がなければ証明のジョブになります"),
            MenuEntry.Item("ジョブの状態を更新", () => _ = Refresh(), !busy),
            MenuEntry.Separator(),
            MenuEntry.Item("タグの選択をすべて外す", () => { tags.Clear(); SyncChoices(); }, tags.Count > 0,
                tags.Count > 0 ? "タグの条件なしになります" : "タグを選んでいません"),
        };

        static readonly Color ChipOn = Theme.Cyan;
        static readonly Color ChipOff = Theme.Muted;
        static readonly Color ChipBad = Theme.Red;

        /// <summary>選んでいるカードの種類とタグ（自動テスト用）</summary>
        public IReadOnlyList<string> SelectedTypes => types;
        public IReadOnlyList<string> SelectedTags => tags;

        /// <summary>別のゲームを開いたとき：そのゲームの集合にない種類・タグの選択を外す（何も残らなければ最初の種類を選ぶ）</summary>
        public void DropUnknown(Game g)
        {
            types.RemoveAll(t => !g.Rules.CardTypes.Contains(t));
            if (types.Count == 0 && g.Rules.CardTypes.Count > 0) types.Add(g.Rules.CardTypes[0]);
            var all = g.Rules.TagSets.SelectMany(t => t.Values).ToList();
            tags.RemoveAll(t => !all.Contains(t));
            SyncChoices();
        }

        /// <summary>選ぶ形の欄（カードの種類・タグ）を、今のゲームの集合に合わせて作り直す</summary>
        public void SyncChoices()
        {
            Game g;
            try { g = getGame(); } catch { return; }
            Fill(typeRow, "カードの種類（どれか）", g.Rules.CardTypes, types, "（集合のノードでカードの種類を加えてください）");
            var tagOptions = g.Rules.TagSets.SelectMany(t => t.Values).Distinct().ToList();
            Fill(tagRow, "タグ（すべて持つ）", tagOptions, tags, "（タグの集合がありません。タグの条件なし）");
        }

        void Fill(VisualElement box, string label, List<string> options, List<string> selected, string empty)
        {
            box.Clear();
            var l = new Label(label) { style = { marginTop = 4, color = Theme.Text } };
            box.Add(l);
            var row = new VisualElement();
            row.style.flexDirection = FlexDirection.Row;
            row.style.flexWrap = Wrap.Wrap;
            Button Chip(string text, Color bg, System.Action click)
            {
                var b = UiTest.Btn(text, click);
                var off = bg == ChipOff;
                b.style.backgroundColor = Theme.Alpha(bg, off ? 0.03f : 0.18f);
                Theme.Border(b.style, 1, Theme.Alpha(bg, off ? 0.3f : 0.85f));
                b.style.color = off ? Theme.Muted : Theme.Bright;
                Theme.Round(b.style, 1);
                return b;
            }
            foreach (var o in options)
            {
                var v = o;
                row.Add(Chip(o, selected.Contains(o) ? ChipOn : ChipOff, () =>
                {
                    if (selected.Contains(v)) selected.Remove(v); else selected.Add(v);
                    SyncChoices();
                }));
            }
            foreach (var bad in selected.Where(x => !options.Contains(x)).ToList())
                row.Add(Chip($"{bad}（集合にない）×", ChipBad, () => { selected.Remove(bad); SyncChoices(); }));
            if (row.childCount == 0) row.Add(new Label(empty) { style = { color = Quiet, fontSize = 12 } });
            box.Add(row);
        }

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
                    ["types"] = new JArray(types),
                    ["tags"] = new JArray(tags),
                    ["both"] = both.value,
                    ["n"] = Math.Max(0, n.value),
                    ["place"] = Places[Math.Max(0, place.index)].Item2,
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
                        Say($"反例があります：試したデッキで {moves} 手進めると、条件に合うカードが {(int)o["count"]} 枚になります（最大 {n.value} 枚を超える）。", Bad);
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
                if (list.Count == 0) jobs.Add(new Label("ジョブはまだありません") { style = { color = Quiet, fontSize = 12 } });
                foreach (var j in list)
                {
                    var st = (string)j["status"];
                    var label = st == "accepted" ? "証明済み" : st == "rejected" ? "差し戻し" : "証明待ち";
                    var l = new Label($"{(string)j["id"]}　[{label}]　{(string)j["title"]}");
                    l.style.whiteSpace = WhiteSpace.Normal;
                    l.style.fontSize = 12;
                    l.style.marginTop = 2;
                    l.style.color = st == "accepted" ? Good : st == "rejected" ? Bad : Quiet;
                    jobs.Add(l);
                }
            }
            catch (Exception e) { Say($"ジョブの一覧を読めません：{e.Message}", Bad); }
        }
    }
}
