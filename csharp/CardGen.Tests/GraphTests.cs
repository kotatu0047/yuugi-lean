using System;
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
        Assert.Contains("範囲のノードが効果につながっていません", structure);
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
}
