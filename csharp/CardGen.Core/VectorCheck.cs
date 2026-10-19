// テストベクトル（Lean の CardGen/Vectors.lean が書き出す「入力」と「正解」の組）の読み書きと、C# の結果との照合。
// 差分テストと、エディタの「C# と照合」（ユーザーのゲームのテストベクトル）の両方で使う。
using System;
using System.Collections.Generic;
using System.Linq;
using Newtonsoft.Json.Linq;

namespace CardGen
{
    /// <summary>テストベクトルの JSON と C# の値の読み書き（カードは名前で指す）</summary>
    public sealed class VectorJson
    {
        readonly Dictionary<string, Card> cards;
        public VectorJson(Dictionary<string, Card> cards) { this.cards = cards; }

        public Card Card(JToken name) => cards[(string)name];

        public Slot ParseSlot(JToken x) =>
            new Slot((int)x["zone"], (int)x["cell"], Card(x["card"]), (bool)x["faceUp"], (int)x["damage"],
                (int)x["atkBonus"], (int)x["defBonus"]);

        public static JObject SlotJson(Slot sl) => new JObject
        {
            ["zone"] = sl.Zone, ["cell"] = sl.Cell, ["card"] = sl.Card.Name, ["faceUp"] = sl.FaceUp, ["damage"] = sl.Damage,
            ["atkBonus"] = sl.AtkBonus, ["defBonus"] = sl.DefBonus,
        };

        public PState ParseState(JToken t) => new PState
        {
            Deck = t["deck"].Select(Card).ToList(),
            Hand = t["hand"].Select(Card).ToList(),
            Grave = t["grave"].Select(Card).ToList(),
            Field = t["field"].Select(ParseSlot).ToList(),
            Life = (int)t["life"],
        };

        public static JObject StateJson(PState s) => new JObject
        {
            ["deck"] = new JArray(s.Deck.Select(c => c.Name)),
            ["hand"] = new JArray(s.Hand.Select(c => c.Name)),
            ["grave"] = new JArray(s.Grave.Select(c => c.Name)),
            ["field"] = new JArray(s.Field.Select(SlotJson)),
            ["life"] = s.Life,
        };

        public static JArray MatchStateJson(MatchState g) => new JArray(StateJson(g.P1), StateJson(g.P2));

        public static string VerdictName(Verdict v) => v switch
        {
            Verdict.Ok => "ok",
            Verdict.SomeLoop => "someLoop",
            Verdict.MultiStable => "multiStable",
            Verdict.CannotHalt => "cannotHalt",
            _ => "noStable",
        };

        public static (bool, int)? ParseTgt(JToken t) => t.Type == JTokenType.Null ? ((bool, int)?)null : ((bool)t[0], (int)t[1]);
        public static List<(bool, int)> ParseNeg(JToken t) => t.Select(x => ((bool)x[0], (int)x[1])).ToList();
        public static List<(int, int)> ParseBlocks(JToken t) => t.Select(x => ((int)x[0], (int)x[1])).ToList();
        public static Cell? ParseCell(JToken c) => c == null || c.Type == JTokenType.Null ? (Cell?)null : new Cell((int)c[0], (int)c[1]);

        public Inst ParseInst(JToken x) => new Inst(Card(x["card"]), (bool)x["controller"], (bool)x["faceUp"], ParseCell(x["cell"]));

        public Choice ParseChoice(JToken c) => (string)c["kind"] switch
        {
            "draw" => Choice.Draw((bool)c["player"]),
            "place" => Choice.Place((bool)c["player"], (int)c["hand"], (int)c["zone"], (int)c["cell"], (bool)c["faceUp"]),
            "attack" => Choice.Attack((bool)c["player"], (int)c["field"],
                c["target"].Type == JTokenType.Null ? (int?)null : (int)c["target"], ParseNeg(c["neg"])),
            "combat" => Choice.Combat((bool)c["player"], c["attackers"].Select(x => (int)x).ToList(), ParseBlocks(c["blocks"]),
                ParseNeg(c["neg"])),
            "mend" => Choice.Mend(),
            "settle" => Choice.Settle(ParseNeg(c["neg"])),
            "discard" => Choice.Discard((bool)c["player"], (int)c["hand"]),
            "trigger" => Choice.Trigger((bool)c["player"], Card(c["card"]), (int)c["effect"], ParseCell(c["cell"]),
                (bool)c["apply"], ParseNeg(c["neg"]), ParseTgt(c["tgt"])),
            _ => Choice.Resolve((bool)c["player"], (int)c["field"], (int)c["effect"], (bool)c["apply"], ParseNeg(c["neg"]), ParseTgt(c["tgt"])),
        };

        public static TChoice ParseTChoice(JToken c) => (string)c["kind"] switch
        {
            "place" => TChoice.Place((int)c["hand"], (int)c["zone"], (int)c["cell"], (bool)c["faceUp"],
                c["pay"].Select(x => (string)x).ToList()),
            "cast" => TChoice.Cast((int)c["hand"], (int)c["zone"], (int)c["cell"], (bool)c["faceUp"],
                c["pay"].Select(x => (string)x).ToList()),
            "resolve" => TChoice.Resolve((bool)c["player"], (int)c["field"], (int)c["effect"], (bool)c["apply"], ParseNeg(c["neg"]),
                ParseTgt(c["tgt"])),
            "settle" => TChoice.Settle(ParseNeg(c["neg"])),
            "pass" => TChoice.Pass(),
            "attack" => TChoice.Attack((int)c["field"],
                c["target"].Type == JTokenType.Null ? (int?)null : (int)c["target"], ParseNeg(c["neg"])),
            "tap" => TChoice.Tap((int)c["field"], (string)c["color"]),
            "oppTap" => TChoice.OppTap((int)c["field"], (string)c["color"]),
            "block" => TChoice.Block(ParseBlocks(c["blocks"]), ParseNeg(c["neg"])),
            "discard" => TChoice.Discard((int)c["hand"]),
            "trigger" => TChoice.Trigger((int)c["index"], (bool)c["skip"], (bool)c["apply"], ParseNeg(c["neg"]), ParseTgt(c["tgt"])),
            _ => TChoice.EndTurn(),
        };

        public static JObject TurnJson(TurnInfo t) => new JObject
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
            ["prio"] = t.Prio,
            ["passes"] = t.Passes,
            ["pending"] = new JArray(t.Pending.Select(e => new JObject
            {
                ["player"] = e.P, ["card"] = e.Card.Name, ["effect"] = e.Eff,
                ["cell"] = e.Cell is Cell c ? new JArray(c.Col, c.Row) : (JToken)JValue.CreateNull(),
            })),
        };

        public static JObject MatchJson(Match m) => new JObject
        {
            ["state"] = MatchStateJson(m.G),
            ["turn"] = TurnJson(m.Turn),
        };

        public static TState ParseTState(JToken t) => new TState(t["on"].Select(x => (bool)x).ToArray(), t["order"].Select(x => (int)x).ToArray());
        public static JObject TStateJson(TState t) => new JObject { ["on"] = new JArray(t.On), ["order"] = new JArray(t.Order) };
    }

    /// <summary>照合の結果：照合した件数と、食い違い（最初のいくつか）</summary>
    public sealed class VectorReport
    {
        public int Checks, Games, Steps, Boards, Timed;
        public List<string> Mismatches = new List<string>();
        public bool Ok => Mismatches.Count == 0;

        internal void Fail(string message)
        {
            if (Mismatches.Count < 20) Mismatches.Add(message);
            else if (Mismatches.Count == 20) Mismatches.Add("（ほかにもあります）");
        }
    }

    /// <summary>
    /// ユーザーのゲームのテストベクトル（lake exe cardgen --game-vectors）を、C# で同じように計算して照合する。
    /// 形式の検査・ターンのある対戦（開始時の状態と、1歩ごとの結果）・無効の関係の盤面・時刻つきの判定の1歩
    /// </summary>
    public static class GameVectors
    {
        public static VectorReport Verify(JObject v)
        {
            var report = new VectorReport();
            var game = IrJson.ParseGame(v["game"]);
            var r = game.Rules;
            var j = new VectorJson(game.Cards.GroupBy(c => c.Name).ToDictionary(g => g.Key, g => g.First()));

            // 形式の検査：誤りの文と順番
            var expected = v["check"].Select(x => (string)x).ToList();
            var actual = Check.Game(game);
            report.Checks = 1;
            if (!expected.SequenceEqual(actual))
                report.Fail($"形式の検査：Lean は [{string.Join("、", expected)}]、C# は [{string.Join("、", actual)}]");

            // ターンのある対戦
            foreach (var g in v["play"])
            {
                report.Games++;
                var decks = g["decks"].Select(d => d.Select(j.Card).ToList()).ToList();
                var m = Match.Start(r, decks[0], decks[1], (bool)g["first"]);
                if (!JToken.DeepEquals(g["start"], VectorJson.MatchJson(m)))
                {
                    report.Fail($"対戦 {report.Games}：開始時の状態が違います");
                    continue;
                }
                int k = 0;
                foreach (var s in g["steps"])
                {
                    k++;
                    report.Steps++;
                    var ch = VectorJson.ParseTChoice(s["choice"]);
                    var next = m.Step(r, ch);
                    var where = $"対戦 {report.Games} の {k} 手目（{s["choice"]["kind"]}）";
                    if (s["result"].Type == JTokenType.Null)
                    {
                        if (next != null) { report.Fail($"{where}：Lean ではできない動きが C# ではできました"); break; }
                        continue;
                    }
                    if (next == null) { report.Fail($"{where}：Lean ではできる動きが C# ではできません"); break; }
                    if (!JToken.DeepEquals(s["result"], VectorJson.MatchJson(next))) { report.Fail($"{where}：結果の盤面が違います"); break; }
                    m = next;
                }
            }

            // 無効の関係の盤面：関係と判定の分類
            foreach (var b in v["boards"])
            {
                report.Boards++;
                var insts = b["insts"].Select(j.ParseInst).ToList();
                var rel = (JArray)b["rel"];
                for (int y = 0; y < insts.Count; y++)
                    for (int x = 0; x < insts.Count; x++)
                        if ((bool)rel[y][x] != Negation.InstRel(insts, y, x))
                            report.Fail($"無効の関係の盤面 {report.Boards}：{insts[y].Card.Name} → {insts[x].Card.Name} が違います");
                var verdict = VectorJson.VerdictName(Negation.AnalyzeBoard(insts));
                if (verdict != (string)b["verdict"])
                    report.Fail($"無効の関係の盤面 {report.Boards}：分類が違います（Lean {b["verdict"]}、C# {verdict}）");
            }

            // 時刻つきの判定（OCG の手順）の1歩
            foreach (var t in v["timed"])
            {
                report.Timed++;
                var insts = t["insts"].Select(j.ParseInst).ToList();
                var next = new TSys(insts).Succ((bool)t["turn"], VectorJson.ParseTState(t["state"]));
                if (!JToken.DeepEquals(t["expected"], new JArray(next.Select(VectorJson.TStateJson))))
                    report.Fail($"時刻つきの判定 {report.Timed}：次の状態が違います");
            }
            return report;
        }
    }
}
