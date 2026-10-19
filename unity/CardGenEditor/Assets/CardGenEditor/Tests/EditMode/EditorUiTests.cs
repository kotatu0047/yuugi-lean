// エディタとテストプレイの画面の自動テスト（Unity Test Framework の EditMode）。
// 画面の要素を作り、ボタンを文字で探して押し（UiTest.Press）、C# の対戦エンジンの状態と記録で結果を確かめる。
using System.Linq;
using NUnit.Framework;
using UnityEngine;
using UnityEngine.UIElements;

namespace CardGen.App.Tests
{
    public class EditorUiTests
    {
        static Game Load(string name) => IrJson.ParseGame(Resources.Load<TextAsset>(name).text);

        [Test]
        public void Every_node_has_a_view_and_an_inspector()
        {
            foreach (var file in new[] { "sample", "mtg" })
            {
                var doc = GraphDoc.FromGame(Load(file));
                var setsNode = doc.Nodes.First(n => n.Kind == NodeKind.Sets);
                var insp = new Inspector { Sets = () => setsNode.Sets };
                foreach (var n in doc.Nodes)
                {
                    Assert.DoesNotThrow(() => new NodeView(n), $"{file}：{n.Kind} の表示");
                    Assert.DoesNotThrow(() => insp.Show(n), $"{file}：{n.Kind} のインスペクタ");
                }
            }
            // 新しく加えたばかりの、どの種類のノードも
            var insp2 = new Inspector();
            foreach (NodeKind k in System.Enum.GetValues(typeof(NodeKind)))
            {
                var n = Node.Make(1, k, 0, 0);
                Assert.DoesNotThrow(() => new NodeView(n), $"{k} の表示");
                Assert.DoesNotThrow(() => insp2.Show(n), $"{k} のインスペクタ");
            }
        }

        [Test]
        public void Candidates_add_a_connected_node()
        {
            var canvas = new GraphCanvas();
            canvas.SetDoc(GraphDoc.FromGame(Load("mtg")));
            var act = canvas.Doc.Nodes.First(n => n.Kind == NodeKind.Activate);
            canvas.ShowCandidatesFor(act);
            Assert.IsTrue(canvas.CandidatesShown);
            var labels = UiTest.Buttons(canvas.CandidatePopup);
            CollectionAssert.IsSupersetOf(labels, new[] { "破壊", "ドロー", "ターンの終わりまでの変化", "打ち消す" });
            CollectionAssert.DoesNotContain(labels, "範囲");
            var before = canvas.Doc.Children(act).Count;
            Assert.IsTrue(UiTest.Press(canvas.CandidatePopup, "打ち消す"));
            var kids = canvas.Doc.Children(act);
            Assert.AreEqual(before + 1, kids.Count);
            var added = kids.Single(k => k.Kind == NodeKind.Counter);
            Assert.AreSame(added, canvas.SelectedNode);
            Assert.Greater(added.X, act.X);
            // 加えた「打ち消す」の候補は範囲だけ
            canvas.ShowCandidatesFor(added);
            CollectionAssert.AreEqual(new[] { "範囲" }, UiTest.Buttons(canvas.CandidatePopup));
        }

        [Test]
        public void Arrange_puts_parents_left_of_children()
        {
            var canvas = new GraphCanvas();
            var doc = GraphDoc.FromGame(Load("sample"));
            foreach (var n in doc.Nodes) { n.X = 500 - n.X; n.Y = n.Id * 7 % 300; }   // ばらばらにする
            canvas.SetDoc(doc);
            var game = doc.ToGame(out _);
            canvas.Arrange();
            foreach (var e in canvas.Doc.Edges) Assert.Less(canvas.Doc.Find(e.From).X, canvas.Doc.Find(e.To).X);
            Assert.AreEqual(IrJson.ToJson(game).ToString(), IrJson.ToJson(canvas.Doc.ToGame(out _)).ToString());
        }

        [Test]
        public void Mtg_test_play_places_a_land_and_taps_it()
        {
            var game = Load("mtg");
            var view = new PlayView();
            view.Start(game);
            var hand = view.CurrentMatch.G.P1.Hand;
            var land = hand.FindIndex(c => c.Mana > 0);
            Assert.GreaterOrEqual(land, 0, "最初の手札に土地がある");
            Assert.IsTrue(view.ShowsPlaceable(true, land), "土地は「置ける」");
            view.SelectHand(true, land);
            Assert.IsTrue(UiTest.Press(view, "戦場に表側で置く"), string.Join(" / ", UiTest.Buttons(view)));
            Assert.AreEqual(1, view.CurrentMatch.G.P1.Field.Count);
            view.SelectField(true, 0);
            Assert.IsTrue(UiTest.Press(view, "タップしてマナを出す"), string.Join(" / ", UiTest.Buttons(view)));
            Assert.AreEqual(1, view.CurrentMatch.Turn.Pool.Count);
            // 2枚目の土地は置けない（1ターンに1枚）
            var land2 = view.CurrentMatch.G.P1.Hand.FindIndex(c => c.Mana > 0);
            if (land2 >= 0) Assert.IsFalse(view.ShowsPlaceable(true, land2));
        }

        [Test]
        public void Combat_scenario_blocks_with_two_bears()
        {
            var view = new PlayView();
            view.Start(Load("mtg"));
            view.Scenario("combat");
            Assert.AreEqual(2, view.CurrentMatch.Turn.Attackers.Count);
            Assert.AreEqual(2, view.CurrentMatch.Turn.Passes);
            Assert.IsTrue(UiTest.Press(view, "このブロックで戦闘する"), string.Join(" / ", UiTest.Buttons(view)));
            var m = view.CurrentMatch;
            Assert.AreEqual(0, m.Turn.Attackers.Count);
            Assert.IsFalse(m.G.P1.Field.Any(s => s.Card.Name == "丘巨人"), "丘巨人は熊2体の4点で破壊される");
            Assert.AreEqual(1, m.G.P2.Field.Count(s => s.Card.Name == "灰色熊"), "熊の1体は破壊され、もう1体は残る");
            Assert.AreEqual(19, m.G.P2.Life, "ブロックされなかったゴブリンの先兵の1点");
        }

        [Test]
        public void Stack_resolves_after_both_players_pass()
        {
            var view = new PlayView();
            view.Start(Load("mtg"));
            view.Scenario("stack");
            Assert.AreEqual(2, view.CurrentMatch.Turn.Stack.Count);
            Assert.IsFalse(UiTest.Buttons(view).Any(b => b.Contains("一番上を解決する")), "パスする前は解決できない");
            Assert.IsTrue(UiTest.Press(view, "相手がパスする"));
            Assert.IsTrue(UiTest.Press(view, "自分がパスする"));
            Assert.IsTrue(UiTest.Press(view, "一番上を解決する"), string.Join(" / ", UiTest.Buttons(view)));
            Assert.AreEqual(1, view.CurrentMatch.Turn.Stack.Count);
            Assert.AreEqual(17, view.CurrentMatch.G.P1.Life, "稲妻の3点");
        }

        [Test]
        public void Shock_kills_the_chosen_target()
        {
            var view = new PlayView();
            view.Start(Load("mtg"));
            view.Scenario("target");
            Assert.IsTrue(UiTest.Press(view, "相手の灰色熊を対象にする"), string.Join(" / ", UiTest.Buttons(view)));
            var opp = view.CurrentMatch.G.P2;
            Assert.IsFalse(opp.Field.Any(s => s.Card.Name == "灰色熊"));
            Assert.IsTrue(opp.Field.Any(s => s.Card.Name == "ゴブリンの先兵"), "対象でないカードはそのまま");
        }

        [Test]
        public void Demo_games_keep_the_board_constraints()
        {
            foreach (var file in new[] { "sample", "mtg" })
            {
                var game = Load(file);
                var view = new PlayView();
                view.Start(game);
                view.Demo(8);
                Assert.IsEmpty(view.CurrentMatch.G.Violations(game.Rules), file);
                Assert.Greater(view.CurrentMatch.G.P1.Field.Count + view.CurrentMatch.G.P2.Field.Count, 0, file);
                Assert.IsFalse(view.Log.Any(l => l.StartsWith("（できません）")), string.Join("\n", view.Log));
            }
        }

        [Test]
        public void Renaming_a_set_value_in_the_inspector_updates_the_cards()
        {
            var doc = GraphDoc.FromGame(Load("mtg"));
            var sets = doc.Nodes.First(n => n.Kind == NodeKind.Sets);
            var insp = new Inspector { Sets = () => sets.Sets, Rename = (k, a, b) => doc.RenameValue(k, a, b) };
            insp.Show(sets);
            Assert.IsTrue(UiTest.Press(insp, "クリーチャー"));
            var field = insp.Query<TextField>().ToList().First(f => f.label != null && f.label.Contains("新しい名前"));
            field.value = "生物";
            Assert.IsTrue(UiTest.Press(insp, "名前を変える"));
            var g = doc.ToGame(out _);
            Assert.IsEmpty(Check.Game(g));
            Assert.IsTrue(g.Cards.Where(c => c.Attack > 0).All(c => c.Type == "生物"));
            CollectionAssert.AreEqual(new[] { "生物" }, g.Rules.Fighters);
        }

        [Test]
        public void Adding_set_values_in_the_inspector()
        {
            var doc = GraphDoc.New();
            var sets = doc.Nodes.First(n => n.Kind == NodeKind.Sets);
            var insp = new Inspector { Sets = () => sets.Sets };
            insp.Show(sets);
            var input = insp.Query<TextField>().ToList().First(f => string.IsNullOrEmpty(f.label));
            input.value = "モンスター、魔法、罠";
            Assert.IsTrue(UiTest.Press(insp, "加える"));
            CollectionAssert.AreEqual(new[] { "モンスター", "魔法", "罠" }, sets.Sets.CardTypes);
            Assert.IsTrue(UiTest.Press(insp, "タグの集合を加える"));
            Assert.AreEqual(1, sets.Sets.TagSets.Count);
        }

        [Test]
        public void Claim_panel_picks_types_and_tags_from_the_sets()
        {
            var game = Load("mtg");
            var panel = new ClaimPanel(() => game, () => "");
            panel.DropUnknown(game);
            CollectionAssert.AreEqual(new[] { "土地" }, panel.SelectedTypes);
            CollectionAssert.IsEmpty(panel.SelectedTags);
            Assert.IsTrue(UiTest.Press(panel, "クリーチャー"));
            CollectionAssert.Contains(panel.SelectedTypes, "クリーチャー");
            Assert.IsTrue(UiTest.Press(panel, "ゴブリン"));
            CollectionAssert.AreEqual(new[] { "ゴブリン" }, panel.SelectedTags);
        }

        // ---- 右クリックのメニュー ----

        static void Pick(System.Collections.Generic.List<MenuEntry> items, string text)
        {
            var it = items.FirstOrDefault(i => i.Text == text && i.Enabled);
            Assert.IsNotNull(it, $"「{text}」がない：{string.Join(" / ", PopupMenu.Texts(items))}");
            it.Action();
        }

        [Test]
        public void Node_menu_connects_disconnects_and_deletes()
        {
            var canvas = new GraphCanvas();
            canvas.SetDoc(GraphDoc.FromGame(Load("mtg")));
            var act = canvas.Doc.Nodes.First(n => n.Kind == NodeKind.Activate);
            var before = canvas.Doc.Children(act).Count;
            var actMenu = canvas.NodeMenu(act);
            Assert.IsTrue(actMenu[0].IsTitle);
            Assert.AreEqual(NodeView.KindColor(NodeKind.Counter), actMenu.First(i => i.Text == "打ち消す").Swatch);
            Pick(actMenu, "打ち消す");
            var counter = canvas.Doc.Children(act).Single(k => k.Kind == NodeKind.Counter);
            Assert.AreEqual(before + 1, canvas.Doc.Children(act).Count);
            // 打ち消すのメニューのつなぎ先は範囲だけ
            CollectionAssert.AreEqual(new[] { "範囲" },
                canvas.NodeMenu(counter).Where(i => i.Swatch != null && !i.IsTitle).Select(i => i.Text).ToArray());
            Pick(canvas.NodeMenu(counter), "入ってくるつなぎを外す");
            Assert.IsFalse(canvas.Doc.Edges.Any(e => e.To == counter.Id));
            var unlinked = canvas.NodeMenu(counter).First(i => i.Text == "入ってくるつなぎを外す");
            Assert.IsFalse(unlinked.Enabled, "つなぎがなければ押せない");
            Assert.AreEqual("どこからもつながっていません", unlinked.Hint);
            Pick(canvas.NodeMenu(counter), "削除");
            Assert.IsNull(canvas.Doc.Find(counter.Id));
            // 集合のノードは削除できない
            var sets = canvas.Doc.Nodes.First(n => n.Kind == NodeKind.Sets);
            var del = canvas.NodeMenu(sets).First(i => i.Text == "削除");
            Assert.IsFalse(del.Enabled);
            Assert.IsTrue(del.Danger);
            StringAssert.Contains("削除できません", del.Hint);
            Assert.IsNotNull(canvas.Doc.Find(sets.Id));
        }

        [Test]
        public void Background_menu_adds_a_node_where_clicked()
        {
            var canvas = new GraphCanvas();
            canvas.SetDoc(GraphDoc.FromGame(Load("sample")));
            var items = canvas.BackgroundMenu(new Vector2(321, 654));
            var texts = PopupMenu.Texts(items);
            CollectionAssert.Contains(texts, "整列");
            CollectionAssert.DoesNotContain(texts, Node.KindLabel(NodeKind.Sets));
            Pick(items, Node.KindLabel(NodeKind.Card));
            var added = canvas.SelectedNode;
            Assert.AreEqual(NodeKind.Card, added.Kind);
            Assert.AreEqual(321, added.X, 0.01);
            Assert.AreEqual(654, added.Y, 0.01);
            Assert.IsFalse(canvas.Doc.Edges.Any(e => e.To == added.Id), "どこにもつながない");
        }

        [Test]
        public void Card_menus_show_the_same_moves_as_the_side_panel()
        {
            var view = new PlayView();
            view.Start(Load("mtg"));
            var land = view.CurrentMatch.G.P1.Hand.FindIndex(c => c.Mana > 0);
            var menu = view.HandMenu(true, land);
            StringAssert.Contains(view.CurrentMatch.G.P1.Hand[land].Name, menu[0].Text);
            // メニューの動きは、右の欄のボタンにもある
            var buttons = UiTest.Buttons(view);
            foreach (var t in menu.Where(i => i.Enabled && !i.IsHeader && !i.IsSeparator && !i.Text.StartsWith("置く向き")))
                CollectionAssert.Contains(buttons, t.Text);
            Assert.IsTrue(PopupMenu.Choose(menu, "戦場に表側で置く"), string.Join(" / ", PopupMenu.Texts(menu)));
            Assert.AreEqual(1, view.CurrentMatch.G.P1.Field.Count);
            Assert.IsTrue(PopupMenu.Choose(view.FieldMenu(true, 0), "タップしてマナを出す"));
            Assert.AreEqual(1, view.CurrentMatch.Turn.Pool.Count);
            // 相手の手札は、自分のターンには置けない（できる動きがない）
            var opp = view.HandMenu(false, 0);
            Assert.IsFalse(opp.Any(i => i.Enabled && !i.IsHeader && !i.IsSeparator && i.Text.Contains("置く")));
            // 空き場所のメニュー：ターン終了で相手のターンになる
            var general = view.GeneralMenu();
            CollectionAssert.Contains(PopupMenu.Texts(general), "自分がパスする");
            Pick(general, "ターン終了");
            Assert.IsFalse(view.CurrentMatch.Turn.Tp);
        }

        [Test]
        public void General_menu_resolves_the_stack()
        {
            var view = new PlayView();
            view.Start(Load("mtg"));
            view.Scenario("stack");
            var end = view.GeneralMenu().First(i => i.Text == "ターン終了");
            Assert.IsFalse(end.Enabled, "スタックがあるとターンを終えられない");
            StringAssert.Contains("スタック", end.Hint);
            Pick(view.GeneralMenu(), "相手がパスする");
            Pick(view.GeneralMenu(), "自分がパスする");
            var menu = view.GeneralMenu();
            Assert.IsTrue(menu[0].IsTitle);
            Assert.AreEqual("今できること", menu[1].Text);
            Assert.IsTrue(PopupMenu.Choose(menu, "一番上を解決する"), string.Join(" / ", PopupMenu.Texts(menu)));
            Assert.AreEqual(1, view.CurrentMatch.Turn.Stack.Count);
            Assert.AreEqual(17, view.CurrentMatch.G.P1.Life, "稲妻の3点");
        }

        [Test]
        public void Problem_nodes_show_the_fault_and_its_reason()
        {
            var canvas = new GraphCanvas();
            canvas.SetDoc(GraphDoc.FromGame(Load("sample")));
            var card = canvas.Doc.Nodes.First(n => n.Kind == NodeKind.Card);
            var destroy = canvas.Doc.Nodes.First(n => n.Kind == NodeKind.Destroy);
            canvas.SetProblems(new System.Collections.Generic.Dictionary<int, string> { [card.Id] = "カード「X」：種類が集合にありません" });
            NodeView View(Node n) => canvas.Query<NodeView>().ToList().Single(v => v.Node == n);
            var bad = View(card);
            Assert.AreEqual("カード「X」：種類が集合にありません", bad.FaultText);
            Assert.AreEqual(DisplayStyle.Flex, bad.Q("fault-tape").style.display.value, "警告テープが出る");
            // 破壊のノードは種類の色が赤でも、警告の演出は出ない
            Assert.AreEqual("", View(destroy).FaultText);
            Assert.AreEqual(DisplayStyle.None, View(destroy).Q("fault-tape").style.display.value);
            // 直れば消える
            canvas.SetProblems(new System.Collections.Generic.Dictionary<int, string>());
            Assert.AreEqual("", View(card).FaultText);
            Assert.AreEqual(DisplayStyle.None, View(card).Q("fault-tape").style.display.value);
        }

        [Test]
        public void Cell_menu_places_a_hand_card_in_that_cell()
        {
            var view = new PlayView();
            view.Start(Load("mtg"));
            var menu = view.CellMenu(true, 0, 5);
            Assert.IsTrue(menu[0].IsTitle);
            var place = menu.First(i => i.Enabled && i.Text.EndsWith("を置く"));
            // 同じカードは1つだけ出る
            var names = menu.Where(i => i.Enabled && i.Text.EndsWith("を置く")).Select(i => i.Text).ToList();
            CollectionAssert.AllItemsAreUnique(names);
            place.Action();
            var f = view.CurrentMatch.G.P1.Field;
            Assert.AreEqual(1, f.Count);
            Assert.AreEqual(5, f[0].Cell, "右クリックしたマスに置かれる");
            // 相手の側のマスには、自分のターンに置ける手札がない（インスタントでマナもない）
            Assert.IsFalse(view.CellMenu(false, 0, 3).Any(i => i.Enabled && i.Text.EndsWith("を置く")));
        }

        [Test]
        public void Field_menu_assigns_blocks_and_fights()
        {
            var view = new PlayView();
            view.Start(Load("mtg"));
            view.Scenario("combat");
            var bear = view.CurrentMatch.G.P2.Field.FindIndex(s => s.Card.Name == "灰色熊");
            var menu = view.FieldMenu(false, bear);
            CollectionAssert.Contains(PopupMenu.Texts(menu), "ブロック");
            Assert.IsTrue(menu.Any(i => i.Enabled && i.Text.Contains("（丘巨人）を止める")), string.Join(" / ", PopupMenu.Texts(menu)));
            Pick(menu, "ブロックしない");
            Assert.IsTrue(PopupMenu.Texts(view.FieldMenu(false, bear)).Contains("✓ ブロックしない"));
            Assert.IsTrue(PopupMenu.Choose(view.FieldMenu(false, bear), "（丘巨人）を止める"));
            Assert.IsTrue(PopupMenu.Choose(view.FieldMenu(false, bear), "で戦闘する"));
            Assert.AreEqual(0, view.CurrentMatch.Turn.Attackers.Count);
        }

        [Test]
        public void Field_menu_chooses_the_target()
        {
            var view = new PlayView();
            view.Start(Load("mtg"));
            view.Scenario("target");
            var bear = view.CurrentMatch.G.P2.Field.FindIndex(s => s.Card.Name == "灰色熊");
            var menu = view.FieldMenu(false, bear);
            Assert.IsTrue(menu.Any(i => i.IsInfo && i.Text.StartsWith("今の攻撃力")), "場のカードの詳細が出る");
            Pick(menu, "このカードを対象にする");
            Assert.IsFalse(view.CurrentMatch.G.P2.Field.Any(s => s.Card.Name == "灰色熊"));
        }

        [Test]
        public void Player_and_general_menus()
        {
            var view = new PlayView();
            view.Start(Load("mtg"));
            var pm = view.PlayerMenu(true);
            Assert.AreEqual("自分", pm[0].Text);
            Assert.AreEqual(view.CurrentMatch.G.P1.Hand.Count, pm.Count(i => i.Text.StartsWith("選ぶ：")));
            Assert.IsTrue(pm.Any(i => i.IsInfo && i.Text.Contains("デッキ")));
            // 場面は MTG 風の見本だけ
            CollectionAssert.Contains(PopupMenu.Texts(view.GeneralMenu()), "場面：スタックで応答");
            var ygo = new PlayView();
            ygo.Start(Load("sample"));
            CollectionAssert.DoesNotContain(PopupMenu.Texts(ygo.GeneralMenu()), "場面：スタックで応答");
            // 両者がパスすると、スタックの一番上を解決できる（場のカードのメニューにも出る）
            view.Scenario("stack");
            Pick(view.GeneralMenu(), "両者がパスする");
            Assert.AreEqual(2, view.CurrentMatch.Turn.Passes);
            var (q, top) = view.CurrentMatch.Turn.Stack[0];
            var k = (q ? view.CurrentMatch.G.P1 : view.CurrentMatch.G.P2).Field.FindIndex(x => TurnInfo.SameSlot(x, top));
            Assert.IsTrue(PopupMenu.Choose(view.FieldMenu(q, k), "一番上を解決する"));
            Assert.AreEqual(1, view.CurrentMatch.Turn.Stack.Count);
        }

        [Test]
        public void Hand_limit_blocks_the_end_of_turn_until_discarded()
        {
            // 遊戯王風の見本は手札の上限 6 枚。何も置かずにターンを終え続けると、後攻は4ターン目に 7 枚になる
            var view = new PlayView();
            view.Start(Load("sample"));
            for (int i = 0; i < 3; i++) Pick(view.GeneralMenu(), "ターン終了");
            var m = view.CurrentMatch;
            Assert.IsFalse(m.Turn.Tp);
            Assert.AreEqual(7, m.G.P2.Hand.Count);
            var end = view.GeneralMenu().First(i => i.Text == "ターン終了");
            Assert.IsFalse(end.Enabled);
            StringAssert.Contains("手札が上限", end.Hint);
            Assert.IsTrue(PopupMenu.Choose(view.HandMenu(false, 0), "墓地へ捨てる"));
            Assert.AreEqual(6, view.CurrentMatch.G.P2.Hand.Count);
            Assert.AreEqual(1, view.CurrentMatch.G.P2.Grave.Count);
            Assert.IsFalse(view.HandMenu(false, 0).Any(i => i.Enabled && i.Text.Contains("墓地へ捨てる")), "上限以下なら捨てられない");
            Pick(view.GeneralMenu(), "ターン終了");
            Assert.IsTrue(view.CurrentMatch.Turn.Tp);
        }

        [Test]
        public void Triggered_effects_wait_and_resolve()
        {
            var view = new PlayView();
            view.Start(Load("mtg"));
            view.Scenario("trigger");
            // 山と森をタップして、エルフの幻想家を置く（置かれたとき1枚引く）
            Assert.IsTrue(PopupMenu.Choose(view.FieldMenu(true, 0), "タップしてマナを出す"));
            Assert.IsTrue(PopupMenu.Choose(view.FieldMenu(true, 1), "タップしてマナを出す"));
            Assert.IsTrue(PopupMenu.Choose(view.HandMenu(true, 0), "で置く"), string.Join(" / ", UiTest.Buttons(view)));
            Assert.AreEqual(1, view.CurrentMatch.Turn.Pending.Count);
            // 待ちがあるうちは、ターンを終えられない
            var end = view.GeneralMenu().First(i => i.Text == "ターン終了");
            Assert.IsFalse(end.Enabled);
            StringAssert.Contains("誘発", end.Hint);
            Assert.IsFalse(UiTest.Buttons(view).Contains("ターン終了"), "上の「ターン終了」も押せない");
            var hand = view.CurrentMatch.G.P1.Hand.Count;
            Assert.IsTrue(UiTest.Press(view, "解決する：エルフの幻想家"), string.Join(" / ", UiTest.Buttons(view)));
            Assert.AreEqual(hand + 1, view.CurrentMatch.G.P1.Hand.Count, "1枚引く");
            Assert.AreEqual(0, view.CurrentMatch.Turn.Pending.Count);
        }

        [Test]
        public void Optional_trigger_can_be_declined()
        {
            var view = new PlayView();
            view.Start(Load("mtg"));
            view.Scenario("trigger");
            // ショック（赤）で相手のゴブリンの放火魔を破壊すると、相手の「〜できる」効果が誘発する
            Assert.IsTrue(PopupMenu.Choose(view.FieldMenu(true, 0), "タップしてマナを出す"));
            var shock = view.CurrentMatch.G.P1.Hand.FindIndex(c => c.Name == "ショック");
            Assert.IsTrue(PopupMenu.Choose(view.HandMenu(true, shock), "で置く"), string.Join(" / ", UiTest.Buttons(view)));
            Pick(view.GeneralMenu(), "両者がパスする");
            Assert.IsTrue(UiTest.Press(view, "一番上を解決する"), string.Join(" / ", UiTest.Buttons(view)));
            Assert.IsTrue(UiTest.Press(view, "ゴブリンの放火魔を対象にする"), string.Join(" / ", UiTest.Buttons(view)));
            Assert.AreEqual(1, view.CurrentMatch.Turn.Pending.Count);
            Assert.IsFalse(view.CurrentMatch.Turn.Pending[0].P, "相手の効果");
            Assert.IsTrue(UiTest.Press(view, "行わない：ゴブリンの放火魔"), string.Join(" / ", UiTest.Buttons(view)));
            Assert.AreEqual(0, view.CurrentMatch.Turn.Pending.Count);
            Assert.AreEqual(20, view.CurrentMatch.G.P1.Life, "行わなかったのでダメージはない");
        }
    }
}
