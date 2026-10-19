using System;
using System.Collections;
using System.IO;
using System.Linq;
using Newtonsoft.Json;
using UnityEngine;
using UnityEngine.TextCore.Text;
using UnityEngine.UIElements;

namespace CardGen.App
{
    /// <summary>
    /// カードゲームジェネレーターのエディタ（実行時のアプリ）。
    /// 左：ノードのキャンバス、右上：選んだノードの編集、右下：検査の結果。
    /// 形式の検査は C# でその場で行い、★と無効の関係の検査は Lean の検査ツールに頼む。
    /// </summary>
    [RequireComponent(typeof(UIDocument))]
    public sealed class CardGenApp : MonoBehaviour
    {
        GraphCanvas canvas;
        PlayView playView;
        VisualElement editorMain;
        Button modeButton;
        Inspector inspector;
        VisualElement results;
        ScrollView resultsScroll;
        Label status;
        TextField pathField;
        TextField commandField;
        ClaimPanel claimPanel;
        Report lastReport;
        bool reportStale;
        bool checking;

        const string PathKey = "cardgen.path";
        const string CommandKey = "cardgen.command";

        void Awake()
        {
            var doc = GetComponent<UIDocument>();
            if (doc.panelSettings == null) doc.panelSettings = Resources.Load<PanelSettings>("CardGenPanelSettings");
        }

        void Start()
        {
            var root = GetComponent<UIDocument>().rootVisualElement;
            Build(root);
            ApplyJapaneseFont(root);
            if (Environment.GetCommandLineArgs().Contains("-cardgen-mtg")) LoadMtgSample(); else LoadSample();
            StartCoroutine(CommandLineActions());
        }

        // ---- 画面の組み立て ----

        static Button MakeButton(string text, System.Action onClick)
        {
            var b = new Button(onClick) { text = text };
            b.style.marginRight = 4;
            return b;
        }

        static VisualElement Row()
        {
            var r = new VisualElement();
            r.style.flexDirection = FlexDirection.Row;
            r.style.alignItems = Align.Center;
            return r;
        }

        void Build(VisualElement root)
        {
            root.style.flexGrow = 1;
            root.style.backgroundColor = new Color(0.13f, 0.13f, 0.14f);
            root.style.color = new Color(0.92f, 0.92f, 0.94f);

            var toolbar = Row();
            toolbar.style.paddingLeft = 8;
            toolbar.style.paddingTop = 6;
            toolbar.style.paddingBottom = 6;
            toolbar.style.backgroundColor = new Color(0.18f, 0.18f, 0.2f);
            toolbar.style.flexWrap = Wrap.Wrap;
            // 折り返したときに下の領域に押しつぶされないようにする
            toolbar.style.flexShrink = 0;
            toolbar.Add(MakeButton("新規", NewDoc));
            toolbar.Add(MakeButton("整列", () => canvas.Arrange()));
            toolbar.Add(MakeButton("見本", LoadSample));
            toolbar.Add(MakeButton("見本（MTG 風）", LoadMtgSample));
            pathField = new TextField { value = PlayerPrefs.GetString(PathKey, DefaultPath()) };
            pathField.style.width = 360;
            toolbar.Add(pathField);
            toolbar.Add(MakeButton("開く", Open));
            toolbar.Add(MakeButton("保存", Save));
            var sep = new VisualElement();
            sep.style.width = 16;
            toolbar.Add(sep);
            toolbar.Add(new Label("追加：") { style = { marginRight = 4 } });
            foreach (NodeKind k in Enum.GetValues(typeof(NodeKind)))
                if (k != NodeKind.Rules && !Node.IsFixed(k)) toolbar.Add(MakeButton(Node.KindLabel(k), () => canvas.AddNode(k)));
            toolbar.Add(MakeButton("削除", () => canvas.RemoveSelected()));
            var sep2 = new VisualElement();
            sep2.style.width = 16;
            toolbar.Add(sep2);
            modeButton = MakeButton("テストプレイ", TogglePlay);
            modeButton.style.unityFontStyleAndWeight = FontStyle.Bold;
            toolbar.Add(modeButton);
            root.Add(toolbar);

            var main = Row();
            main.style.flexGrow = 1;
            main.style.alignItems = Align.Stretch;
            canvas = new GraphCanvas();
            canvas.Selected += n => inspector.Show(n);
            canvas.Changed += OnModelChanged;
            main.Add(canvas);

            var side = new VisualElement();
            side.style.width = 420;
            side.style.backgroundColor = new Color(0.16f, 0.16f, 0.18f);
            side.style.borderLeftWidth = 1;
            side.style.borderLeftColor = new Color(0.3f, 0.3f, 0.33f);
            inspector = new Inspector();
            inspector.Sets = () => canvas.Doc.Nodes.FirstOrDefault(x => x.Kind == NodeKind.Sets)?.Sets;
            inspector.Rename = (k, from, to) =>
            {
                canvas.Doc.RenameValue(k, from, to);
                canvas.Rebuild();
            };
            inspector.Edited += n => { canvas.RefreshNode(n); OnModelChanged(); };
            var inspScroll = new ScrollView();
            inspScroll.style.height = new Length(42, LengthUnit.Percent);
            inspScroll.Add(inspector);
            side.Add(inspScroll);
            PopupMenu.Attach(inspScroll, _ => canvas.SelectedNode != null ? canvas.NodeMenu(canvas.SelectedNode)
                : new System.Collections.Generic.List<MenuEntry>
                  {
                      MenuEntry.Title("ノードの編集"),
                      MenuEntry.Item("ノードを選んでいません", null, false, "キャンバスでノードをクリックしてください"),
                  });

            var checkRow = Row();
            checkRow.style.paddingLeft = 12;
            checkRow.style.paddingTop = 6;
            checkRow.style.paddingBottom = 6;
            checkRow.style.borderTopWidth = 1;
            checkRow.style.borderTopColor = new Color(0.3f, 0.3f, 0.33f);
            var checkButton = MakeButton("Lean で検査", () => _ = RunLeanCheck());
            checkButton.style.unityFontStyleAndWeight = FontStyle.Bold;
            checkRow.Add(checkButton);
            commandField = new TextField { value = PlayerPrefs.GetString(CommandKey, CheckerClient.DefaultCommand) };
            commandField.style.flexGrow = 1;
            commandField.style.flexShrink = 1;
            commandField.tooltip = "検査ツールを動かすコマンド（最後の - で標準入力から読む）";
            checkRow.Add(commandField);
            side.Add(checkRow);

            var resScroll = new ScrollView();
            resultsScroll = resScroll;
            resScroll.style.flexGrow = 1;
            results = new VisualElement();
            results.style.paddingLeft = 12;
            results.style.paddingRight = 12;
            results.style.paddingBottom = 12;
            resScroll.Add(results);
            claimPanel = new ClaimPanel(() => canvas.Doc.ToGame(out _), () => commandField.value);
            resScroll.Add(claimPanel);
            PopupMenu.Attach(resScroll, _ => ResultsMenu());
            side.Add(resScroll);
            main.Add(side);
            root.Add(main);
            editorMain = main;
            playView = new PlayView { Exit = TogglePlay };
            playView.style.display = DisplayStyle.None;
            root.Add(playView);

            status = new Label();
            status.style.paddingLeft = 8;
            status.style.paddingTop = 3;
            status.style.paddingBottom = 3;
            status.style.fontSize = 11;
            status.style.backgroundColor = new Color(0.1f, 0.1f, 0.11f);
            root.Add(status);
        }

        /// <summary>既定の UI のフォントは日本語を含まないので、OS の日本語フォントを使う</summary>
        static void ApplyJapaneseFont(VisualElement root)
        {
            foreach (var family in new[] { "Yu Gothic UI", "Meiryo UI", "Meiryo", "MS Gothic" })
            {
                try
                {
                    var fa = FontAsset.CreateFontAsset(family, "Regular");
                    if (fa == null) continue;
                    root.style.unityFontDefinition = FontDefinition.FromSDFFont(fa);
                    return;
                }
                catch (Exception) { }
            }
        }

        static string DefaultPath() =>
            Path.Combine(Environment.GetFolderPath(Environment.SpecialFolder.MyDocuments), "cardgame.json");

        /// <summary>検査の結果の欄の右クリックのメニュー</summary>
        System.Collections.Generic.List<MenuEntry> ResultsMenu() => new System.Collections.Generic.List<MenuEntry>
        {
            MenuEntry.Title("検査の結果", lastReport == null ? "まだ Lean で検査していません" : reportStale ? "編集したあとは未実行" : null),
            MenuEntry.Item("Lean で検査", () => _ = RunLeanCheck(), !checking, checking ? "検査しています…" : "★と無効の関係を検査します"),
            MenuEntry.Item("結果をコピーする", () => GUIUtility.systemCopyBuffer =
                string.Join("\n", results.Query<Label>().ToList().Select(l => l.text)), hint: "クリップボードへ"),
            MenuEntry.Separator(),
            MenuEntry.Header("移動"),
            MenuEntry.Item("一番上へ", () => resultsScroll.scrollOffset = Vector2.zero),
            MenuEntry.Item("一番下へ", () => resultsScroll.scrollOffset = new Vector2(0, 100000)),
        };

        // ---- テストプレイ ----

        bool playing;

        void TogglePlay()
        {
            if (!playing)
            {
                var game = canvas.Doc.ToGame(out var structure);
                var errors = structure.Concat(Check.Game(game)).ToList();
                if (errors.Count > 0) { status.text = "形式の問題を直してからテストプレイしてください"; return; }
                if (game.Cards.Count == 0) { status.text = "カードがありません"; return; }
                playView.Start(game);
            }
            playing = !playing;
            editorMain.style.display = playing ? DisplayStyle.None : DisplayStyle.Flex;
            playView.style.display = playing ? DisplayStyle.Flex : DisplayStyle.None;
            modeButton.text = playing ? "エディタに戻る" : "テストプレイ";
            status.text = playing ? "テストプレイ中" : "エディタ";
        }

        // ---- ファイル ----

        void SetDoc(GraphDoc doc, string message)
        {
            canvas.SetDoc(doc);
            claimPanel?.DropUnknown(doc.ToGame(out _));
            inspector.Show(null);
            lastReport = null;
            OnModelChanged();
            status.text = message;
        }

        void NewDoc()
        {
            SetDoc(GraphDoc.New(), "新しいゲームを作りました（集合のノードで、カードの種類などを決めてください）");
        }

        void LoadSample()
        {
            var asset = Resources.Load<UnityEngine.TextAsset>("sample");
            var sample = IrJson.ParseGame(asset.text);
            SetDoc(GraphDoc.FromGame(sample), $"見本（入力例のルールとカード{sample.Cards.Count}枚）を読み込みました");
        }

        void LoadMtgSample()
        {
            var asset = Resources.Load<UnityEngine.TextAsset>("mtg");
            var sample = IrJson.ParseGame(asset.text);
            SetDoc(GraphDoc.FromGame(sample), $"MTG 風の見本（土地・マナ・タップ・ブロック。カード{sample.Cards.Count}枚）を読み込みました");
        }

        void Open()
        {
            try
            {
                var path = pathField.value;
                var o = Newtonsoft.Json.Linq.JObject.Parse(File.ReadAllText(path));
                var old = o["version"]?.ToString();
                var upgraded = IrJson.Upgrade(o);
                var v = Game.CurrentVersion;
                SetDoc(GraphDoc.FromGame(IrJson.ParseGame(o)), upgraded
                    ? $"開きました：{path}（版 {old} のファイルなので版 {v} に上げました。" +
                      (old == "2" ? "ターンのルールは既定の値です。" : "") +
                      $"ゾーンはマス目の上にない状態です。保存すると版 {v} で書き出します）"
                    : $"開きました：{path}");
                PlayerPrefs.SetString(PathKey, path);
            }
            catch (Exception e) { status.text = $"開けません：{e.Message}"; }
        }

        void Save()
        {
            try
            {
                var path = pathField.value;
                var game = canvas.Doc.ToGame(out _);
                File.WriteAllText(path, IrJson.ToJson(game).ToString(Formatting.Indented));
                PlayerPrefs.SetString(PathKey, path);
                status.text = $"保存しました：{path}";
            }
            catch (Exception e) { status.text = $"保存できません：{e.Message}"; }
        }

        // ---- 検査 ----

        static Label Text(string s, int size = 12, Color? color = null, bool bold = false)
        {
            var l = new Label(s);
            l.style.whiteSpace = WhiteSpace.Normal;
            l.style.fontSize = size;
            if (color.HasValue) l.style.color = color.Value;
            if (bold) l.style.unityFontStyleAndWeight = FontStyle.Bold;
            return l;
        }

        static Color StatusColor(string s) => s switch
        {
            "proved" => new Color(0.45f, 0.8f, 0.5f),
            "counterexample" => new Color(0.95f, 0.45f, 0.4f),
            "choice" => new Color(0.95f, 0.75f, 0.35f),
            _ => new Color(0.7f, 0.7f, 0.75f),
        };

        static VisualElement Badge(string status)
        {
            var l = Text(Report.StatusLabel(status), 11, Color.black, true);
            l.style.backgroundColor = StatusColor(status);
            l.style.paddingLeft = 6;
            l.style.paddingRight = 6;
            l.style.marginRight = 6;
            l.style.borderTopLeftRadius = l.style.borderTopRightRadius = l.style.borderBottomLeftRadius = l.style.borderBottomRightRadius = 3;
            l.style.alignSelf = Align.FlexStart;
            return l;
        }

        static void Section(VisualElement parent, string title)
        {
            var l = Text(title, 14, Color.white, true);
            l.style.marginTop = 12;
            l.style.marginBottom = 4;
            parent.Add(l);
        }

        /// <summary>ノードが変わったら、形式の検査をその場でやり直す</summary>
        void OnModelChanged()
        {
            if (lastReport != null) reportStale = true;
            claimPanel?.SyncChoices();
            Render();
        }

        void Render()
        {
            results.Clear();
            var game = canvas.Doc.ToGame(out var structure);
            var errors = structure.Concat(Check.Game(game)).ToList();
            canvas.SetProblems(ProblemNodes(errors));

            Section(results, "形式の検査（その場で）");
            if (errors.Count == 0) results.Add(Text("問題ありません", 12, StatusColor("proved")));
            foreach (var e in errors) results.Add(Text("・" + e, 12, StatusColor("counterexample")));

            Section(results, "Lean による検査" + (reportStale ? "（編集後は未実行）" : ""));
            if (checking) { results.Add(Text("検査しています…")); return; }
            if (lastReport == null) { results.Add(Text("「Lean で検査」を押すと、ルールから導いた性質（★）と無効の関係を検査します。", 12, new Color(0.7f, 0.7f, 0.75f))); return; }
            RenderReport(lastReport);
        }

        System.Collections.Generic.IEnumerable<int> ProblemNodes(System.Collections.Generic.List<string> errors)
        {
            foreach (var n in canvas.Doc.Nodes)
            {
                var key = n.Kind == NodeKind.Card ? $"カード「{n.Card.Name}」" : n.Kind == NodeKind.Zone ? $"ゾーン「{n.Zone.Name}」" : n.Kind == NodeKind.Rules ? "ルール：" : null;
                if (key != null && errors.Any(e => e.StartsWith(key))) yield return n.Id;
            }
        }

        void RenderReport(Report r)
        {
            if (!r.Ok)
            {
                foreach (var e in r.Errors) results.Add(Text("・" + e, 12, StatusColor("counterexample")));
                return;
            }
            results.Add(Text("★ ルールから導いた性質", 12, Color.white, true));
            foreach (var c in r.Claims)
            {
                var row = Row();
                row.style.alignItems = Align.FlexStart;
                row.style.marginTop = 4;
                row.Add(Badge(c.Status));
                var col = new VisualElement();
                col.style.flexShrink = 1;
                col.Add(Text(c.Text, 12, Color.white));
                col.Add(Text("根拠：" + string.Join("、", c.Grounds), 10, new Color(0.65f, 0.65f, 0.7f)));
                row.Add(col);
                results.Add(row);
            }
            if (r.Negation != null)
            {
                var t = Text("無効の関係", 12, Color.white, true);
                t.style.marginTop = 10;
                results.Add(t);
                var row = Row();
                row.style.alignItems = Align.FlexStart;
                row.Add(Badge(r.Negation.Status));
                var msg = Text(r.Negation.Message, 12, Color.white);
                msg.style.flexShrink = 1;
                row.Add(msg);
                results.Add(row);
                foreach (var g in r.Negation.Groups)
                {
                    var box = new VisualElement();
                    box.style.marginTop = 6;
                    box.style.paddingLeft = 8;
                    box.style.borderLeftWidth = 3;
                    box.style.borderLeftColor = StatusColor(g.Status);
                    box.Add(Text("循環：" + string.Join(" ⇄ ", g.Cards), 12, Color.white));
                    box.Add(Text($"[{Report.StatusLabel(g.Status)}] {g.Message}", 11, StatusColor(g.Status)));
                    if (g.Board.Count > 0)
                        box.Add(Text("盤面：" + string.Join("、", g.Board.Select(b => (b.Side == "self" ? "自分：" : "相手：") + b.Card)), 11, new Color(0.8f, 0.8f, 0.85f)));
                    if (!string.IsNullOrEmpty(g.Detail))
                        box.Add(Text("参考：" + g.Detail, 10, new Color(0.65f, 0.65f, 0.7f)));
                    results.Add(box);
                }
            }
        }

        async System.Threading.Tasks.Task RunLeanCheck()
        {
            if (checking) return;
            var game = canvas.Doc.ToGame(out var structure);
            if (structure.Count > 0) { status.text = "つなぎ方の問題を直してから検査してください"; return; }
            checking = true;
            reportStale = false;
            Render();
            PlayerPrefs.SetString(CommandKey, commandField.value);
            try
            {
                var output = await CheckerClient.Run(commandField.value, IrJson.ToJson(game).ToString(Formatting.None));
                lastReport = Report.Parse(output);
                status.text = "Lean による検査が終わりました";
            }
            catch (Exception e)
            {
                lastReport = null;
                status.text = $"検査ツールを動かせません：{e.Message}";
            }
            checking = false;
            Render();
        }

        // ---- コマンドライン（動作確認用）----
        //   -cardgen-mtg                      最初に MTG 風の見本を読み込む
        //   -cardgen-arrange                  ノードを木の形に並べ直す（「整列」）
        //   -cardgen-candidates <種類の名前>   その種類の最初のノードの、つなぎ先の候補を出す（例：Activate）
        //   -cardgen-select <ノードの番号>   そのノードを選ぶ（Sets・Axioms などの種類の名前なら、その種類の最初のノード）
        //   -cardgen-focus <ノードの番号>    そのノードが見えるようにキャンバスを動かす
        //   -cardgen-check                    Lean で検査する
        //   -cardgen-results-end              検査の結果を一番下まで送る
        //   -cardgen-play <手数>              テストプレイを始め、置ける手札を交互に置く
        //   -cardgen-scenario combat|stack    テストプレイで、戦闘（ブロックの割り当て）かスタックの場面を作る（MTG 風の見本）
        //   -cardgen-claim                    命題の欄の値でジョブを作る（反例探し）
        //   -cardgen-menu node|play|card      右クリックのメニューを出す（最初の発動のノード／テストプレイの空き場所／自分の最初の手札）
        //   -cardgen-screenshot <パス>        画面を保存して終了する

        static string Arg(string name)
        {
            var args = Environment.GetCommandLineArgs();
            var i = Array.IndexOf(args, name);
            return i >= 0 && i + 1 < args.Length ? args[i + 1] : null;
        }

        IEnumerator CommandLineActions()
        {
            var args = Environment.GetCommandLineArgs();
            var select = Arg("-cardgen-select");
            if (select != null && int.TryParse(select, out var id))
            {
                var n = canvas.Doc.Find(id);
                if (n != null) canvas.Select(n);
            }
            else if (select != null && Enum.TryParse<NodeKind>(select, true, out var kind))
            {
                // 種類の名前でも選べる（例：-cardgen-select Sets）
                var n = canvas.Doc.Nodes.FirstOrDefault(x => x.Kind == kind);
                if (n != null) canvas.Select(n);
            }
            var focus = Arg("-cardgen-focus");
            if (focus != null && int.TryParse(focus, out var fid))
            {
                yield return null;
                var n = canvas.Doc.Find(fid);
                if (n != null) canvas.Focus(n);
            }
            if (args.Contains("-cardgen-arrange"))
            {
                yield return null;
                canvas.Arrange();
            }
            var cand = Arg("-cardgen-candidates");
            if (cand != null && Enum.TryParse<NodeKind>(cand, true, out var ckind))
            {
                for (int i = 0; i < 3; i++) yield return null;
                var n = canvas.Doc.Nodes.FirstOrDefault(x => x.Kind == ckind);
                if (n != null) { canvas.Focus(n); yield return null; canvas.ShowCandidatesFor(n); }
            }
            if (args.Contains("-cardgen-check"))
            {
                var task = RunLeanCheck();
                while (!task.IsCompleted) yield return null;
            }
            if (args.Contains("-cardgen-claim"))
            {
                var task = claimPanel.Submit();
                while (!task.IsCompleted) yield return null;
            }
            if (args.Contains("-cardgen-play"))
            {
                TogglePlay();
                var demo = Arg("-cardgen-play");
                if (demo != null && int.TryParse(demo, out var moves)) playView.Demo(moves);
                var scene = Arg("-cardgen-scenario");
                if (scene != null) playView.Scenario(scene);
            }
            var menu = Arg("-cardgen-menu");
            if (menu != null)
            {
                for (int i = 0; i < 5; i++) yield return null;
                if (menu == "node")
                {
                    var n = canvas.Doc.Nodes.FirstOrDefault(x => x.Kind == NodeKind.Activate);
                    if (n != null) canvas.OpenMenuFor(n);
                }
                else if (menu == "play")
                {
                    var b = playView.worldBound;
                    PopupMenu.Open(playView, new Vector2(b.x + b.width * 0.35f, b.y + b.height * 0.3f), playView.GeneralMenu());
                }
                else if (menu == "card")
                {
                    var b = playView.worldBound;
                    PopupMenu.Open(playView, new Vector2(b.x + b.width * 0.25f, b.y + b.height * 0.55f), playView.HandMenu(true, 0));
                }
            }
            if (args.Contains("-cardgen-results-end"))
            {
                for (int i = 0; i < 5; i++) yield return null;
                resultsScroll.scrollOffset = new Vector2(0, 100000);
            }
            var shot = Arg("-cardgen-screenshot");
            if (shot != null)
            {
                for (int i = 0; i < 30; i++) yield return null;
                yield return new WaitForEndOfFrame();
                var tex = ScreenCapture.CaptureScreenshotAsTexture();
                File.WriteAllBytes(shot, tex.EncodeToPNG());
                Debug.Log($"CardGen: screenshot {tex.width}x{tex.height} -> {shot}");
                Application.Quit();
            }
        }
    }
}
