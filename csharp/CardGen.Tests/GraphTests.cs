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
}
