using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using CardGen;
using Newtonsoft.Json.Linq;
using Xunit;

public class GraphTests
{
    static Game Sample() => IrJson.ParseGame(File.ReadAllText(Path.Combine(AppContext.BaseDirectory, "sample.json")));

    [Fact]
    public void Sample_round_trips_through_graph()
    {
        var g = Sample();
        var doc = GraphDoc.FromGame(g);
        var back = doc.ToGame(out var structure);
        Assert.Empty(structure);
        Assert.True(JToken.DeepEquals(IrJson.ToJson(g), IrJson.ToJson(back)));
    }

    [Fact]
    public void Connect_checks_kinds_and_replaces_parent()
    {
        var doc = new GraphDoc();
        doc.Nodes.Add(Node.Make(1, NodeKind.Card, 0, 0));
        doc.Nodes.Add(Node.Make(2, NodeKind.Negate, 0, 0));
        doc.Nodes.Add(Node.Make(3, NodeKind.Selector, 0, 0));
        doc.Nodes.Add(Node.Make(4, NodeKind.Selector, 0, 0));
        Assert.False(doc.Connect(1, 3));
        Assert.True(doc.Connect(1, 2));
        Assert.True(doc.Connect(2, 3));
        Assert.True(doc.Connect(2, 4));
        // 無効には範囲を1つだけつなぐ
        Assert.Single(doc.Edges, e => e.From == 2);
        Assert.Equal(4, doc.Edges.Single(e => e.From == 2).To);
    }

    [Fact]
    public void Structure_problems_are_reported()
    {
        var doc = new GraphDoc();
        doc.Nodes.Add(Node.Make(1, NodeKind.Card, 0, 0));
        doc.Nodes.Add(Node.Make(2, NodeKind.Negate, 0, 0));
        doc.Nodes.Add(Node.Make(3, NodeKind.Selector, 0, 0));
        doc.Connect(1, 2);
        doc.ToGame(out var structure);
        Assert.Contains("ルールのノードがありません", structure);
        Assert.Contains("カード「」の無効の効果に、範囲がつながっていません", structure);
        Assert.Contains("範囲のノードがつながっていません", structure);
    }

    [Fact]
    public void Vector_cards_round_trip_through_graph()
    {
        // 手札に戻す・ドローを含むカードもグラフを通して元に戻る
        var v = JObject.Parse(File.ReadAllText(Path.Combine(AppContext.BaseDirectory, "vectors.json")));
        var g = new Game { Rules = IrJson.ParseRules(v["rules"]), Cards = ((JArray)v["cards"]).Select(IrJson.ParseCard).ToList() };
        var back = GraphDoc.FromGame(g).ToGame(out var structure);
        Assert.Empty(structure);
        Assert.True(JToken.DeepEquals(IrJson.ToJson(g), IrJson.ToJson(back)));
    }

    [Fact]
    public void Activate_takes_actions()
    {
        var doc = new GraphDoc();
        doc.Nodes.Add(Node.Make(1, NodeKind.Card, 0, 0));
        doc.Nodes.Add(Node.Make(2, NodeKind.Activate, 0, 0));
        doc.Nodes.Add(Node.Make(3, NodeKind.Draw, 0, 0));
        doc.Nodes.Add(Node.Make(4, NodeKind.Bounce, 0, 100));
        doc.Nodes.Add(Node.Make(5, NodeKind.Selector, 0, 100));
        Assert.True(doc.Connect(1, 2));
        Assert.True(doc.Connect(2, 3));
        Assert.True(doc.Connect(2, 4));
        Assert.False(doc.Connect(2, 5));
        Assert.True(doc.Connect(4, 5));
        doc.Find(3).DrawCount = 2;
        var g = doc.ToGame(out _);
        var act = Assert.IsType<Activated>(g.Cards[0].Effects[0]);
        Assert.Equal(2, Assert.IsType<DrawCards>(act.Actions[0]).Count);
        Assert.IsType<Bounce>(act.Actions[1]);
    }

    [Fact]
    public void Report_parses_cardgen_output()
    {
        const string json = @"{""version"":1,""ok"":true,""errors"":[],""claims"":[{""text"":""t"",""grounds"":[""g""],""status"":""proved"",""theorem"":""CardGen.derived_valid""}],
          ""negation"":{""status"":""choice"",""message"":""m"",""edges"":[[""a"",""b""]],""groups"":[{""cards"":[""a"",""b""],""status"":""choice"",""message"":""x"",""board"":[{""card"":""a"",""side"":""self""}]}],""theorem"":null}}";
        var r = Report.Parse(json);
        Assert.True(r.Ok);
        Assert.Equal("証明済み", Report.StatusLabel(r.Claims[0].Status));
        Assert.Equal("self", r.Negation.Groups[0].Board[0].Side);
        Assert.Null(r.Negation.Theorem);
    }

    [Fact]
    public void Axioms_and_sets_are_fixed()
    {
        var doc = GraphDoc.New();
        Assert.Contains(doc.Nodes, n => n.Kind == NodeKind.Axioms);
        var sets = doc.Nodes.Single(n => n.Kind == NodeKind.Sets);
        var rules = doc.Nodes.Single(n => n.Kind == NodeKind.Rules);
        // 公理・集合・ルールの順に上から並ぶ
        Assert.True(doc.Nodes.Single(n => n.Kind == NodeKind.Axioms).Y < sets.Y && sets.Y < rules.Y);
        foreach (var n in doc.Nodes.Where(n => Node.IsFixed(n.Kind)).ToList()) doc.Remove(n.Id);
        Assert.Equal(3, doc.Nodes.Count);
        // カードの種類・マナの色・タグの集合は集合のノードから
        sets.Sets.CardTypes.Add("土地");
        sets.Sets.TagSets.Add(new TagSet { Name = "色", Values = new List<string> { "赤" } });
        var g = doc.ToGame(out var structure);
        Assert.Empty(structure);
        Assert.Equal(new[] { "土地" }, g.Rules.CardTypes);
        Assert.Equal("色", g.Rules.TagSets.Single().Name);
    }

    [Fact]
    public void Renaming_a_value_updates_every_use()
    {
        var src = File.ReadAllText(Path.Combine(AppContext.BaseDirectory, "mtg.json"));
        var doc = GraphDoc.FromGame(IrJson.ParseGame(src));
        doc.RenameValue(SetKind.CardType, "クリーチャー", "生物");
        doc.RenameValue(SetKind.ManaColor, "赤", "紅");
        doc.RenameValue(SetKind.Tag, "ゴブリン", "小鬼");
        var g = doc.ToGame(out var structure);
        Assert.Empty(structure);
        Assert.Empty(Check.Game(g));
        Assert.Contains("生物", g.Rules.CardTypes);
        Assert.DoesNotContain("クリーチャー", g.Rules.CardTypes);
        Assert.Equal(new[] { "生物" }, g.Rules.Fighters);
        Assert.Contains("紅", g.Rules.ManaColors);
        var goblin = g.Cards.First(c => c.Name == "ゴブリンの先兵");
        Assert.Equal("生物", goblin.Type);
        Assert.Equal(new[] { "紅" }, goblin.ColorCost);
        Assert.Contains("小鬼", goblin.Tags);
        Assert.Equal(new[] { "紅", "緑" }, g.Cards.First(c => c.Name == "カープルーザンの森").ManaChoice);
        Assert.Equal("紅", g.Cards.First(c => c.Name == "山").ManaColor);
    }

    [Fact]
    public void Candidates_and_auto_layout()
    {
        Assert.Equal(new[] { NodeKind.Zone }, GraphDoc.Candidates(NodeKind.Rules));
        Assert.Contains(NodeKind.Pump, GraphDoc.Candidates(NodeKind.Activate));
        Assert.Equal(new[] { NodeKind.Selector }, GraphDoc.Candidates(NodeKind.Destroy));
        Assert.Empty(GraphDoc.Candidates(NodeKind.Selector));

        var doc = GraphDoc.FromGame(Sample());
        var card = doc.Nodes.First(n => n.Kind == NodeKind.Card);
        var before = doc.ToGame(out _);
        var act = doc.AddChild(card, NodeKind.Activate, n => 100);
        Assert.Contains(act, doc.Children(card));
        Assert.True(act.X > card.X);
        // 並べ直しても、中間表現は変わらない（子の順番は上から下のまま）
        doc.Nodes.Remove(act);
        doc.Edges.RemoveAll(e => e.To == act.Id);
        doc.AutoLayout(n => 100, n => 220);
        Assert.True(JToken.DeepEquals(IrJson.ToJson(before), IrJson.ToJson(doc.ToGame(out var st))));
        Assert.Empty(st);
        // 親は子より左にあり、ノードは重ならない
        foreach (var e in doc.Edges) Assert.True(doc.Find(e.From).X < doc.Find(e.To).X);
        var boxes = doc.Nodes.Select(n => (n.X, n.Y)).ToList();
        Assert.Equal(boxes.Count, boxes.Distinct().Count());
    }

    [Fact]
    public void Test_play_decks_have_lands_in_every_opening_hand()
    {
        var game = IrJson.ParseGame(File.ReadAllText(Path.Combine(AppContext.BaseDirectory, "mtg.json")));
        for (int seed = 1; seed <= 50; seed++)
        {
            var rng = new Random(seed);
            foreach (var deck in new[] { DeckBuilder.Make(game, rng), DeckBuilder.Make(game, rng) })
            {
                Assert.Equal(game.Rules.DeckSize, deck.Count);
                var hand = deck.Take(game.Rules.HandSize).ToList();
                Assert.InRange(hand.Count(c => c.Mana > 0), 2, 4);
                Assert.InRange(deck.Count(c => c.Mana > 0), 15, 17);
                // 土地は1種類に偏らない
                Assert.True(deck.Where(c => c.Mana > 0).GroupBy(c => c.Name).Count() >= 3);
            }
        }
        // 遊戯王の見本（マナを出すカードがない）は、一覧を繰り返して混ぜる
        var sample = Sample();
        Assert.Equal(sample.Rules.DeckSize, DeckBuilder.Make(sample, new Random(1)).Count);
    }
}
