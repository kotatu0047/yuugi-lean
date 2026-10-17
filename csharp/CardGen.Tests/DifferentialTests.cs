// Lean の定義（lake exe cardgen --vectors で書き出したテストベクトル）と C# の結果を照合する。
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using CardGen;
using Newtonsoft.Json.Linq;
using Xunit;

public class DifferentialTests
{
    static readonly JObject V = JObject.Parse(File.ReadAllText(Path.Combine(AppContext.BaseDirectory, "vectors.json")));
    static readonly Rules R = IrJson.ParseRules(V["rules"]);
    static readonly Dictionary<string, Card> Cards =
        ((JArray)V["cards"]).Select(IrJson.ParseCard).ToDictionary(c => c.Name);

    static View ParseView(JToken t) => new View((string)t["type"], t["tags"].Select(x => (string)x).ToList(),
        (bool)t["mine"], (bool)t["faceUp"], (bool)t["isSelf"]);

    static PState ParseState(JToken t) => new PState
    {
        Deck = t["deck"].Select(x => Cards[(string)x]).ToList(),
        Hand = t["hand"].Select(x => Cards[(string)x]).ToList(),
        Grave = t["grave"].Select(x => Cards[(string)x]).ToList(),
        Field = t["field"].Select(x => new Slot((int)x["zone"], Cards[(string)x["card"]], (bool)x["faceUp"])).ToList(),
    };

    static JObject StateJson(PState s) => new JObject
    {
        ["deck"] = new JArray(s.Deck.Select(c => c.Name)),
        ["hand"] = new JArray(s.Hand.Select(c => c.Name)),
        ["grave"] = new JArray(s.Grave.Select(c => c.Name)),
        ["field"] = new JArray(s.Field.Select(sl => new JObject
            { ["zone"] = sl.Zone, ["card"] = sl.Card.Name, ["faceUp"] = sl.FaceUp })),
    };

    static string VerdictName(Verdict v) => v switch
    {
        Verdict.Ok => "ok",
        Verdict.SomeLoop => "someLoop",
        Verdict.MultiStable => "multiStable",
        Verdict.CannotHalt => "cannotHalt",
        _ => "noStable",
    };

    [Fact]
    public void Selector_matches_like_Lean()
    {
        var bad = V["selector"].Where(c =>
            IrJson.ParseSelector(c["selector"]).Matches(ParseView(c["view"])) != (bool)c["expected"]).ToList();
        Assert.True(bad.Count == 0, $"{bad.Count} 件不一致。最初：{bad.FirstOrDefault()}");
    }

    [Fact]
    public void Check_reports_same_errors_as_Lean()
    {
        foreach (var c in V["check"])
        {
            var expected = c["errors"].Select(x => (string)x).ToList();
            Assert.Equal(expected, Check.Game(IrJson.ParseGame(c["game"])));
        }
    }

    [Fact]
    public void Destroy_like_Lean()
    {
        foreach (var c in V["destroy"])
        {
            var result = ParseState(c["state"]).Destroy(R, IrJson.ParseSelector(c["selector"]), (bool)c["mine"]);
            Assert.True(JToken.DeepEquals(c["expected"], StateJson(result)), $"不一致：{c}");
        }
    }

    [Fact]
    public void Boards_like_Lean()
    {
        foreach (var c in V["boards"])
        {
            var insts = c["insts"].Select(x => new Inst(Cards[(string)x["card"]], (bool)x["controller"], (bool)x["faceUp"])).ToList();
            var rel = (JArray)c["rel"];
            for (int y = 0; y < insts.Count; y++)
                for (int x = 0; x < insts.Count; x++)
                    Assert.Equal((bool)rel[y][x], Negation.InstRel(insts, y, x));
            var verdict = (string)c["verdict"];
            Assert.Equal(verdict, VerdictName(Negation.AnalyzeBoard(insts)));
            // 安定な状態の数は分類と食い違わない
            var stables = Negation.StableStates(insts).Count;
            if (verdict == "noStable") Assert.Equal(0, stables);
            else if (verdict == "multiStable") Assert.True(stables > 1);
            else if (verdict == "ok" || verdict == "someLoop") Assert.Equal(1, stables);
        }
    }

    static Choice ParseChoice(JToken c) => (string)c["kind"] switch
    {
        "draw" => Choice.Draw((bool)c["player"]),
        "place" => Choice.Place((bool)c["player"], (int)c["hand"], (int)c["zone"], (bool)c["faceUp"]),
        _ => Choice.Resolve((bool)c["player"], (int)c["field"], (int)c["effect"], (bool)c["apply"]),
    };

    static JArray MatchJson(MatchState g) => new JArray(StateJson(g.P1), StateJson(g.P2));

    [Fact]
    public void Play_like_Lean()
    {
        var rules = IrJson.ParseRules(V["playRules"]);
        int games = 0, steps = 0;
        foreach (var game in V["play"])
        {
            var decks = game["decks"].Select(d => d.Select(x => Cards[(string)x]).ToList()).ToList();
            var g = MatchState.Start(rules, decks[0], decks[1]);
            Assert.True(JToken.DeepEquals(game["start"], MatchJson(g)), "開始時の状態が違います");
            foreach (var st in game["steps"])
            {
                var next = g.Step(rules, ParseChoice(st["choice"]));
                if (st["result"].Type == JTokenType.Null)
                    Assert.True(next == null, $"Lean ではできない動きが C# ではできました：{st["choice"]}");
                else
                {
                    Assert.True(next != null, $"Lean ではできる動きが C# ではできません：{st["choice"]}");
                    Assert.True(JToken.DeepEquals(st["result"], MatchJson(next)), $"結果が違います：{st["choice"]}");
                    Assert.Empty(next.Violations(rules));
                    g = next;
                }
                steps++;
            }
            games++;
        }
        Assert.Equal(40, games);
        Assert.Equal(1600, steps);
    }

    [Fact]
    public void Sample_json_round_trips()
    {
        var src = JToken.Parse(File.ReadAllText(Path.Combine(AppContext.BaseDirectory, "sample.json")));
        var g = IrJson.ParseGame(src);
        Assert.Empty(Check.Game(g));
        Assert.True(JToken.DeepEquals(src, IrJson.ToJson(g)));
    }

    [Fact]
    public void Missing_field_is_rejected()
    {
        Assert.Throws<FormatException>(() => IrJson.ParseGame("{\"version\": 1}"));
    }
}
