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

    static Slot ParseSlot(JToken x) =>
        new Slot((int)x["zone"], (int)x["cell"], Cards[(string)x["card"]], (bool)x["faceUp"], (int)x["damage"]);

    static JObject SlotJson(Slot sl) => new JObject
        { ["zone"] = sl.Zone, ["cell"] = sl.Cell, ["card"] = sl.Card.Name, ["faceUp"] = sl.FaceUp, ["damage"] = sl.Damage };

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
        "combat" => Choice.Combat((bool)c["player"], c["attackers"].Select(x => (int)x).ToList(), ParseBlocks(c["blocks"]),
            ParseNeg(c["neg"])),
        "mend" => Choice.Mend(),
        _ => Choice.Resolve((bool)c["player"], (int)c["field"], (int)c["effect"], (bool)c["apply"], ParseNeg(c["neg"])),
    };

    static List<(bool, int)> ParseNeg(JToken t) => t.Select(x => ((bool)x[0], (int)x[1])).ToList();

    static List<(int, int)> ParseBlocks(JToken t) => t.Select(x => ((int)x[0], (int)x[1])).ToList();

    [Fact]
    public void Attack_values_like_Lean()
    {
        foreach (var c in V["attack"])
        {
            var st = (JArray)c["state"];
            var g = new MatchState { P1 = ParseState(st[0]), P2 = ParseState(st[1]) };
            var neg = ParseNeg(c["neg"]);
            var expected = (JArray)c["expected"];
            var defense = (JArray)c["defense"];
            foreach (var (q, qi) in new[] { (true, 0), (false, 1) })
            {
                var f = g.Get(q).Field;
                for (int j = 0; j < f.Count; j++)
                {
                    Assert.Equal((int)expected[qi][j], g.AtkOf(R, neg, (q, j), f[j]));
                    Assert.Equal((int)defense[qi][j], g.DefOf(R, neg, (q, j), f[j]));
                }
            }
        }
    }

    [Fact]
    public void Combat_like_Lean()
    {
        foreach (var c in V["combat"])
        {
            var st = (JArray)c["state"];
            var g = new MatchState { P1 = ParseState(st[0]), P2 = ParseState(st[1]) };
            var next = g.Combat(R, ParseNeg(c["neg"]), (bool)c["player"], c["attackers"].Select(x => (int)x).ToList(),
                ParseBlocks(c["blocks"]));
            Assert.True(JToken.DeepEquals(c["expected"], MatchJson(next)), $"不一致：{c}\n実際：{MatchJson(next)}");
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
        "place" => TChoice.Place((int)c["hand"], (int)c["zone"], (int)c["cell"], (bool)c["faceUp"],
            c["pay"].Select(x => (string)x).ToList()),
        "cast" => TChoice.Cast((int)c["hand"], (int)c["zone"], (int)c["cell"], (bool)c["faceUp"],
            c["pay"].Select(x => (string)x).ToList()),
        "resolve" => TChoice.Resolve((bool)c["player"], (int)c["field"], (int)c["effect"], (bool)c["apply"], ParseNeg(c["neg"])),
        "attack" => TChoice.Attack((int)c["field"],
            c["target"].Type == JTokenType.Null ? (int?)null : (int)c["target"], ParseNeg(c["neg"])),
        "tap" => TChoice.Tap((int)c["field"], (string)c["color"]),
        "oppTap" => TChoice.OppTap((int)c["field"], (string)c["color"]),
        "block" => TChoice.Block(ParseBlocks(c["blocks"]), ParseNeg(c["neg"])),
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
        ["pool"] = new JArray(t.Pool),
        ["oppPool"] = new JArray(t.OppPool),
        ["tapped"] = new JArray(t.Tapped.Select(SlotJson)),
        ["oppTapped"] = new JArray(t.OppTapped.Select(SlotJson)),
        ["attackers"] = new JArray(t.Attackers.Select(SlotJson)),
        ["blocked"] = new JArray(t.Blocked.Select(SlotJson)),
        ["stack"] = new JArray(t.Stack.Select(x => new JArray(x.player, SlotJson(x.slot)))),
        ["made"] = t.Made,
        ["spent"] = t.Spent,
        ["decked"] = t.Decked == null ? JValue.CreateNull() : new JValue(t.Decked.Value),
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
        Assert.True(ok > 400);
    }

    [Fact]
    public void Mtg_sample_round_trips_and_plays()
    {
        var src = JToken.Parse(File.ReadAllText(Path.Combine(AppContext.BaseDirectory, "mtg.json")));
        var g = IrJson.ParseGame(src);
        Assert.Empty(Check.Game(g));
        Assert.True(JToken.DeepEquals(src, IrJson.ToJson(g)));
        Assert.True(JToken.DeepEquals(src, IrJson.ToJson(GraphDoc.FromGame(g).ToGame(out _))));
        // Lean の CardGen/Mtg.lean と同じ流れ：山を置いてタップし、ゴブリンの先兵を置く。3ターン目に攻撃し、相手がゴブリンの先兵でブロックする
        var c = g.Cards.ToDictionary(x => x.Name);
        var deck = new[] { "山", "山", "ゴブリンの先兵", "灰色熊", "稲妻", "山", "森" }.Select(n => c[n])
            .Concat(Enumerable.Range(0, 33).Select(i => c[i % 2 == 0 ? "山" : "灰色熊"])).ToList();
        var r = g.Rules;
        var m = Match.Start(r, deck, deck, true);
        var turn1 = new[] { TChoice.Place(0, 0, 0, true), TChoice.Tap(0), TChoice.Place(1, 0, 1, true, new List<string> { "赤" }) };
        foreach (var ch in turn1.Append(TChoice.EndTurn()).Concat(turn1).Append(TChoice.EndTurn()))
            m = m.Step(r, ch) ?? throw new Exception("できない動き");
        m = m.Step(r, TChoice.Attack(1, null, new List<(bool, int)>()));
        Assert.Single(m.Turn.Attackers);
        Assert.Null(m.Step(r, TChoice.EndTurn()));
        var none = new List<(bool, int)>();
        var blocked = m.Step(r, TChoice.Block(new List<(int, int)> { (1, 0) }, none));
        Assert.Single(blocked.G.P1.Field);
        Assert.Single(blocked.G.P2.Field);
        Assert.Equal(20, blocked.G.P2.Life);
        var unblocked = m.Step(r, TChoice.Block(new List<(int, int)>(), none));
        Assert.Equal(19, unblocked.G.P2.Life);

        // インスタントとスタック：自分が紅蓮地獄を唱え、相手が応答して稲妻を唱える。稲妻から解決する
        Slot S(int i, string n, int d = 0) => new Slot(0, i, c[n], true, d);
        PState P(string third, string second, params string[] hand) => new PState
        {
            Deck = new List<Card> { c["山"], c["山"] }, Hand = hand.Select(n => c[n]).ToList(), Life = 20,
            Field = new List<Slot> { S(0, "山"), S(1, second), S(2, third) },
        };
        var duel = new Match
        {
            G = new MatchState { P1 = P("丘巨人", "山", "紅蓮地獄"), P2 = P("ゴブリンの先兵", "カープルーザンの森", "稲妻", "治癒の軟膏") },
            Turn = new TurnInfo { Tp = true, Count = 3 },
        };
        var red = new List<string> { "赤" };
        var d = duel;
        foreach (var ch in new[] { TChoice.Tap(0), TChoice.Tap(1), TChoice.Place(0, 1, 0, true, new List<string> { "赤", "赤" }),
                                   TChoice.OppTap(0), TChoice.Cast(0, 1, 0, true, red) })
            d = d.Step(r, ch) ?? throw new Exception($"できない動き：{ch.Kind}");
        Assert.Equal(new[] { false, true }, d.Turn.Stack.Select(x => x.player));
        Assert.Null(d.Step(r, TChoice.Resolve(true, 3, 0, true)));
        d = d.Step(r, TChoice.Resolve(false, 3, 0, true));
        Assert.Equal(17, d.G.P1.Life);
        d = d.Step(r, TChoice.Resolve(true, 3, 0, true));
        Assert.Equal(2, d.G.P1.Field[2].Damage);
        Assert.Equal(new[] { "稲妻", "ゴブリンの先兵" }, d.G.P2.Grave.Select(x => x.Name));
        d = d.Step(r, TChoice.EndTurn());
        Assert.All(d.G.P1.Field, sl => Assert.Equal(0, sl.Damage));
        // カープルーザンの森は赤か緑を選ぶ
        Assert.Equal(new[] { "緑" }, duel.Step(r, TChoice.OppTap(1, "緑")).Turn.OppPool);
        Assert.Null(duel.Step(r, TChoice.OppTap(1, "白")));
    }

    [Fact]
    public void Sample_json_round_trips()
    {
        var src = JToken.Parse(File.ReadAllText(Path.Combine(AppContext.BaseDirectory, "sample.json")));
        var g = IrJson.ParseGame(src);
        Assert.Empty(Check.Game(g));
        Assert.True(JToken.DeepEquals(src, IrJson.ToJson(g)));
    }

    /// <summary>版 8 で加えたもの（インスタント・スタック・選べるマナの色）を除く（遊戯王の見本はどれも使っていない）</summary>
    static JObject WithoutInstants(JObject o)
    {
        o["version"] = 7;
        ((JObject)o["rules"]).Remove("instants");
        ((JObject)o["rules"]).Remove("stack");
        foreach (var c in o["cards"]) { ((JObject)c).Remove("manaChoice"); ((JObject)c).Remove("trample"); }
        return o;
    }

    [Fact]
    public void Version_7_is_upgraded()
    {
        var src = (JObject)JToken.Parse(File.ReadAllText(Path.Combine(AppContext.BaseDirectory, "sample.json")));
        var o = WithoutInstants((JObject)src.DeepClone());
        Assert.Throws<FormatException>(() => IrJson.ParseGame(o.DeepClone()));
        Assert.True(IrJson.Upgrade(o));
        Assert.True(JToken.DeepEquals(src, o));
        Assert.False(IrJson.Upgrade(o));
    }

    /// <summary>版 7 で加えたタグの集合を除く</summary>
    static JObject WithoutTagSets(JObject o)
    {
        o = WithoutInstants(o);
        o["version"] = 6;
        ((JObject)o["rules"]).Remove("tagSets");
        return o;
    }

    [Fact]
    public void Version_6_is_upgraded()
    {
        var src = (JObject)JToken.Parse(File.ReadAllText(Path.Combine(AppContext.BaseDirectory, "sample.json")));
        src["rules"]["tagSets"] = new JArray();
        var o = WithoutTagSets((JObject)src.DeepClone());
        Assert.Throws<FormatException>(() => IrJson.ParseGame(o.DeepClone()));
        Assert.True(IrJson.Upgrade(o));
        Assert.True(JToken.DeepEquals(src, o));
        Assert.False(IrJson.Upgrade(o));
    }

    static JObject WithoutColors(JObject o)
    {
        o = WithoutTagSets(o);
        o["version"] = 5;
        ((JObject)o["rules"]).Remove("manaColors");
        foreach (var c in o["cards"]) { ((JObject)c).Remove("colorCost"); ((JObject)c).Remove("manaColor"); }
        return o;
    }

    [Fact]
    public void Version_5_is_upgraded()
    {
        var src = (JObject)JToken.Parse(File.ReadAllText(Path.Combine(AppContext.BaseDirectory, "sample.json")));
        src["rules"]["tagSets"] = new JArray();
        var o = WithoutColors((JObject)src.DeepClone());
        Assert.Throws<FormatException>(() => IrJson.ParseGame(o.DeepClone()));
        Assert.True(IrJson.Upgrade(o));
        Assert.True(JToken.DeepEquals(src, o));
        Assert.False(IrJson.Upgrade(o));
    }

    [Fact]
    public void Auto_pay_pays_colors_first()
    {
        var bear = new Card { Name = "熊", Cost = 1, ColorCost = new List<string> { "緑" } };
        Assert.Equal(new[] { "緑", "" }, TurnInfo.AutoPay(bear, new List<string> { "赤", "緑", "" }));
        Assert.Equal(new[] { "緑", "赤" }, TurnInfo.AutoPay(bear, new List<string> { "赤", "緑" }));
        Assert.Null(TurnInfo.AutoPay(bear, new List<string> { "赤", "赤" }));
        Assert.Null(TurnInfo.AutoPay(bear, new List<string> { "緑" }));
    }

    static JObject WithoutMana(JObject o)
    {
        o = WithoutColors(o);
        o["version"] = 4;
        foreach (var k in new[] { "placeLimits", "attackTaps", "summoningSickness", "blocking" }) ((JObject)o["rules"]).Remove(k);
        foreach (var c in o["cards"]) { ((JObject)c).Remove("cost"); ((JObject)c).Remove("mana"); }
        return o;
    }

    [Fact]
    public void Version_4_is_upgraded()
    {
        var src = (JObject)JToken.Parse(File.ReadAllText(Path.Combine(AppContext.BaseDirectory, "sample.json")));
        src["rules"]["tagSets"] = new JArray();
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
        expected.Rules.TagSets.Clear();
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
