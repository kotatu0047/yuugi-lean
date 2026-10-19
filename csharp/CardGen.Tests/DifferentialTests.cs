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
        (bool)t["mine"], (bool)t["faceUp"], (bool)t["isSelf"], (bool)t["adjacent"], (bool)t["sameColumn"]);

    static Slot ParseSlot(JToken x) => new Slot((int)x["zone"], (int)x["cell"], Cards[(string)x["card"]], (bool)x["faceUp"]);

    static JObject SlotJson(Slot sl) => new JObject
        { ["zone"] = sl.Zone, ["cell"] = sl.Cell, ["card"] = sl.Card.Name, ["faceUp"] = sl.FaceUp };

    static PState ParseState(JToken t) => new PState
    {
        Deck = t["deck"].Select(x => Cards[(string)x]).ToList(),
        Hand = t["hand"].Select(x => Cards[(string)x]).ToList(),
        Grave = t["grave"].Select(x => Cards[(string)x]).ToList(),
        Field = t["field"].Select(ParseSlot).ToList(),
        Life = (int)t["life"],
    };

    static JObject StateJson(PState s) => new JObject
    {
        ["deck"] = new JArray(s.Deck.Select(c => c.Name)),
        ["hand"] = new JArray(s.Hand.Select(c => c.Name)),
        ["grave"] = new JArray(s.Grave.Select(c => c.Name)),
        ["field"] = new JArray(s.Field.Select(SlotJson)),
        ["life"] = s.Life,
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
            var src = c["src"];
            var cell = src["cell"].Type == JTokenType.Null ? (Cell?)null : new Cell((int)src["cell"]["col"], (int)src["cell"]["row"]);
            var result = ParseState(c["state"]).Destroy(R, IrJson.ParseSelector(c["selector"]), (bool)c["owner"],
                new Src((bool)src["player"], cell));
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

    [Fact]
    public void Timed_step_like_Lean()
    {
        static TState Parse(JToken t) => new TState(t["on"].Select(x => (bool)x).ToArray(), t["order"].Select(x => (int)x).ToArray());
        static JObject Json(TState t) => new JObject { ["on"] = new JArray(t.On), ["order"] = new JArray(t.Order) };
        foreach (var c in V["timed"])
        {
            var insts = c["insts"].Select(x => new Inst(Cards[(string)x["card"]], (bool)x["controller"], (bool)x["faceUp"])).ToList();
            var next = new TSys(insts).Succ((bool)c["turn"], Parse(c["state"]));
            Assert.True(JToken.DeepEquals(c["expected"], new JArray(next.Select(Json))), $"不一致：{c}");
        }
    }

    static Choice ParseChoice(JToken c) => (string)c["kind"] switch
    {
        "draw" => Choice.Draw((bool)c["player"]),
        "place" => Choice.Place((bool)c["player"], (int)c["hand"], (int)c["zone"], (int)c["cell"], (bool)c["faceUp"]),
        "attack" => Choice.Attack((bool)c["player"], (int)c["field"],
            c["target"].Type == JTokenType.Null ? (int?)null : (int)c["target"], ParseNeg(c["neg"])),
        _ => Choice.Resolve((bool)c["player"], (int)c["field"], (int)c["effect"], (bool)c["apply"]),
    };

    static List<(bool, int)> ParseNeg(JToken t) => t.Select(x => ((bool)x[0], (int)x[1])).ToList();

    [Fact]
    public void Attack_values_like_Lean()
    {
        foreach (var c in V["attack"])
        {
            var st = (JArray)c["state"];
            var g = new MatchState { P1 = ParseState(st[0]), P2 = ParseState(st[1]) };
            var neg = ParseNeg(c["neg"]);
            var expected = (JArray)c["expected"];
            foreach (var (q, qi) in new[] { (true, 0), (false, 1) })
            {
                var f = g.Get(q).Field;
                for (int j = 0; j < f.Count; j++)
                    Assert.Equal((int)expected[qi][j], g.AtkOf(R, neg, (q, j), f[j]));
            }
        }
    }

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
        Assert.Equal(80, games);
        Assert.Equal(4000, steps);
    }

    static TChoice ParseTChoice(JToken c) => (string)c["kind"] switch
    {
        "place" => TChoice.Place((int)c["hand"], (int)c["zone"], (int)c["cell"], (bool)c["faceUp"]),
        "resolve" => TChoice.Resolve((bool)c["player"], (int)c["field"], (int)c["effect"], (bool)c["apply"]),
        "attack" => TChoice.Attack((int)c["field"],
            c["target"].Type == JTokenType.Null ? (int?)null : (int)c["target"], ParseNeg(c["neg"])),
        "tap" => TChoice.Tap((int)c["field"]),
        _ => TChoice.EndTurn(),
    };

    static JObject TurnJson(TurnInfo t) => new JObject
    {
        ["tp"] = t.Tp,
        ["count"] = t.Count,
        ["summons"] = t.Summons,
        ["attacked"] = new JArray(t.Attacked.Select(SlotJson)),
        ["placed"] = new JArray(t.Placed),
        ["entered"] = new JArray(t.Entered.Select(SlotJson)),
        ["pool"] = t.Pool,
        ["tapped"] = new JArray(t.Tapped.Select(SlotJson)),
        ["oppTapped"] = new JArray(t.OppTapped.Select(SlotJson)),
    };

    static JObject MatchJson(Match m) => new JObject
    {
        ["state"] = new JArray(StateJson(m.G.P1), StateJson(m.G.P2)),
        ["turn"] = TurnJson(m.Turn),
    };

    [Fact]
    public void Turn_play_like_Lean()
    {
        int games = 0, steps = 0, ok = 0;
        foreach (var game in V["turnPlay"])
        {
            var r = IrJson.ParseRules(game["rules"]);
            var decks = game["decks"].Select(d => d.Select(x => Cards[(string)x]).ToList()).ToList();
            var m = Match.Start(r, decks[0], decks[1], (bool)game["first"]);
            Assert.True(JToken.DeepEquals(game["start"], MatchJson(m)), $"開始時の状態が不一致：{game["start"]}");
            foreach (var s in game["steps"])
            {
                var next = m.Step(r, ParseTChoice(s["choice"]));
                if (s["result"].Type == JTokenType.Null)
                    Assert.True(next == null, $"Lean ではできない動きが C# ではできた：{s["choice"]}");
                else
                {
                    Assert.True(next != null, $"Lean ではできる動きが C# ではできない：{s["choice"]}");
                    Assert.True(JToken.DeepEquals(s["result"], MatchJson(next)), $"不一致：{s["choice"]}\n期待：{s["result"]}\n実際：{MatchJson(next)}");
                    m = next;
                    ok++;
                }
                steps++;
            }
            games++;
        }
        Assert.Equal(80, games);
        Assert.Equal(4800, steps);
        Assert.True(ok > 600);
    }

    [Fact]
    public void Sample_json_round_trips()
    {
        var src = JToken.Parse(File.ReadAllText(Path.Combine(AppContext.BaseDirectory, "sample.json")));
        var g = IrJson.ParseGame(src);
        Assert.Empty(Check.Game(g));
        Assert.True(JToken.DeepEquals(src, IrJson.ToJson(g)));
    }

    /// <summary>見本から、版 3 にないもの（マスの位置・マスの関係）を除いた JSON と、それを上げたときに期待する Game</summary>
    /// <summary>版 5 で加えたもの（マナ・タップなど）を除く（見本はどれも使っていない）</summary>
    static JObject WithoutMana(JObject o)
    {
        o["version"] = 4;
        foreach (var k in new[] { "placeLimits", "attackTaps", "summoningSickness" }) ((JObject)o["rules"]).Remove(k);
        foreach (var c in o["cards"]) { ((JObject)c).Remove("cost"); ((JObject)c).Remove("mana"); }
        return o;
    }

    [Fact]
    public void Version_4_is_upgraded()
    {
        var src = (JObject)JToken.Parse(File.ReadAllText(Path.Combine(AppContext.BaseDirectory, "sample.json")));
        var o = WithoutMana((JObject)src.DeepClone());
        Assert.Throws<FormatException>(() => IrJson.ParseGame(o.DeepClone()));
        Assert.True(IrJson.Upgrade(o));
        Assert.True(JToken.DeepEquals(src, o));
        Assert.False(IrJson.Upgrade(o));
    }

    static (JObject old, Game expected) WithoutGrid()
    {
        var o = (JObject)JToken.Parse(File.ReadAllText(Path.Combine(AppContext.BaseDirectory, "sample.json")));
        var expected = IrJson.ParseGame(o.DeepClone());
        foreach (var z in expected.Rules.Zones) z.Cells.Clear();
        foreach (var c in expected.Cards)
            foreach (var e in c.Effects)
            {
                var sels = e switch
                {
                    Negate n => new[] { n.Target },
                    Boost b => new[] { b.Target },
                    Activated a => a.Actions.Select(x => x is Destroy d ? d.Target : x is Bounce bo ? bo.Target : null)
                        .Where(x => x != null).ToArray(),
                    _ => new Selector[0],
                };
                foreach (var sel in sels) sel.Near = Near.Any;
            }
        o = WithoutMana(o);
        o["version"] = 3;
        foreach (var z in o["rules"]["zones"]) ((JObject)z).Remove("cells");
        foreach (var p in ((JArray)o["cards"]).Descendants().OfType<JProperty>().Where(p => p.Name == "near").ToList()) p.Remove();
        return (o, expected);
    }

    [Fact]
    public void Version_3_is_upgraded()
    {
        var (o, expected) = WithoutGrid();
        Assert.Throws<FormatException>(() => IrJson.ParseGame(o.DeepClone()));
        Assert.True(IrJson.Upgrade(o));
        Assert.True(JToken.DeepEquals(IrJson.ToJson(expected), IrJson.ToJson(IrJson.ParseGame(o))));
        Assert.False(IrJson.Upgrade(o));
    }

    [Fact]
    public void Version_2_is_upgraded()
    {
        var (o, expected) = WithoutGrid();
        o["version"] = 2;
        foreach (var k in new[] { "summonsPerTurn", "drawPerTurn", "firstTurnDraw", "firstTurnAttack" }) ((JObject)o["rules"]).Remove(k);
        Assert.Throws<FormatException>(() => IrJson.ParseGame(o.DeepClone()));
        Assert.True(IrJson.Upgrade(o));
        Assert.True(JToken.DeepEquals(IrJson.ToJson(expected), IrJson.ToJson(IrJson.ParseGame(o))));
        Assert.False(IrJson.Upgrade(o));
    }

    [Fact]
    public void Missing_field_is_rejected()
    {
        Assert.Throws<FormatException>(() => IrJson.ParseGame("{\"version\": 1}"));
    }
}
