// 中間表現と JSON の変換（Lean の自動導出と同じ形）。
// Option 以外のフィールドはすべて必須で、足りなければ FormatException を投げる。
using System;
using System.Collections.Generic;
using System.Linq;
using Newtonsoft.Json.Linq;

namespace CardGen
{
    public static class IrJson
    {
        static JToken Field(JObject o, string name) =>
            o.TryGetValue(name, out var v) && v.Type != JTokenType.Null
                ? v : throw new FormatException($"フィールド「{name}」がありません");

        static JObject Obj(JToken t) =>
            t as JObject ?? throw new FormatException("オブジェクトが必要です");

        static string Str(JObject o, string name) =>
            Field(o, name).Type == JTokenType.String ? (string)Field(o, name)! : throw new FormatException($"「{name}」は文字列が必要です");

        static int Int(JObject o, string name) =>
            Field(o, name).Type == JTokenType.Integer ? (int)Field(o, name) : throw new FormatException($"「{name}」は数が必要です");

        static bool Bool(JObject o, string name) =>
            Field(o, name).Type == JTokenType.Boolean ? (bool)Field(o, name) : throw new FormatException($"「{name}」は真偽が必要です");

        static List<string> Strs(JObject o, string name) =>
            (Field(o, name) as JArray ?? throw new FormatException($"「{name}」は配列が必要です"))
                .Select(t => t.Type == JTokenType.String ? (string)t! : throw new FormatException($"「{name}」は文字列の配列が必要です"))
                .ToList();

        static List<T> Arr<T>(JObject o, string name, Func<JToken, T> f) =>
            (Field(o, name) as JArray ?? throw new FormatException($"「{name}」は配列が必要です")).Select(f).ToList();

        static T Enum<T>(JObject o, string name, params (string, T)[] cases)
        {
            var s = Str(o, name);
            foreach (var (k, v) in cases) if (k == s) return v;
            throw new FormatException($"「{name}」の値「{s}」は使えません");
        }

        /// <summary>{"ctor": {...}} の形を読む</summary>
        static (string, JObject) Tagged(JToken t)
        {
            var o = Obj(t);
            if (o.Count != 1) throw new FormatException("効果・動きは1つのキーを持つオブジェクトが必要です");
            var p = o.Properties().First();
            return (p.Name, Obj(p.Value));
        }

        public static Selector ParseSelector(JToken t)
        {
            var o = Obj(t);
            return new Selector
            {
                Types = Strs(o, "types"),
                Tags = Strs(o, "tags"),
                Side = Enum(o, "side", ("self", Side.Self), ("opp", Side.Opp), ("both", Side.Both)),
                FaceUpOnly = Bool(o, "faceUpOnly"),
                ExcludeSelf = Bool(o, "excludeSelf"),
            };
        }

        static Action ParseAction(JToken t)
        {
            var (k, o) = Tagged(t);
            return k switch
            {
                "destroy" => new Destroy(ParseSelector(Field(o, "target"))),
                "bounce" => new Bounce(ParseSelector(Field(o, "target"))),
                "draw" => new DrawCards(Int(o, "count")),
                "damage" => new Damage(Int(o, "amount")),
                "heal" => new Heal(Int(o, "amount")),
                _ => throw new FormatException($"動き「{k}」は使えません"),
            };
        }

        static Effect ParseEffect(JToken t)
        {
            var (k, o) = Tagged(t);
            return k switch
            {
                "activated" => new Activated(Arr(o, "actions", ParseAction)),
                "negate" => new Negate(ParseSelector(Field(o, "target"))),
                "boost" => new Boost(ParseSelector(Field(o, "target")), Int(o, "amount")),
                _ => throw new FormatException($"効果「{k}」は使えません"),
            };
        }

        public static Card ParseCard(JToken t)
        {
            var o = Obj(t);
            return new Card
            {
                Name = Str(o, "name"),
                Type = Str(o, "type"),
                Tags = Strs(o, "tags"),
                Effects = Arr(o, "effects", ParseEffect),
                Attack = Int(o, "attack"),
                Defense = Int(o, "defense"),
            };
        }

        static Zone ParseZone(JToken t)
        {
            var o = Obj(t);
            return new Zone
            {
                Name = Str(o, "name"),
                Count = Int(o, "count"),
                Capacity = Enum(o, "capacity", ("one", Capacity.One), ("many", Capacity.Many)),
                Role = Enum(o, "role", ("deck", ZoneRole.Deck), ("grave", ZoneRole.Grave), ("plain", ZoneRole.Plain)),
                OnField = Bool(o, "onField"),
                Admits = Strs(o, "admits"),
            };
        }

        public static Rules ParseRules(JToken t)
        {
            var o = Obj(t);
            return new Rules
            {
                CardTypes = Strs(o, "cardTypes"),
                DeckSize = Int(o, "deckSize"),
                HandSize = Int(o, "handSize"),
                Zones = Arr(o, "zones", ParseZone),
                Life = Int(o, "life"),
                Fighters = Strs(o, "fighters"),
                SummonsPerTurn = Int(o, "summonsPerTurn"),
                DrawPerTurn = Int(o, "drawPerTurn"),
                FirstTurnDraw = Bool(o, "firstTurnDraw"),
                FirstTurnAttack = Bool(o, "firstTurnAttack"),
            };
        }

        public static Game ParseGame(JToken t)
        {
            var o = Obj(t);
            return new Game
            {
                Version = Int(o, "version"),
                Rules = ParseRules(Field(o, "rules")),
                Cards = Arr(o, "cards", ParseCard),
            };
        }

        public static Game ParseGame(string json) => ParseGame(JToken.Parse(json));

        /// <summary>
        /// 古い版の中間表現を今の版に上げる（エディタで開くとき用）。版 2 → 3 はターンのルールを既定の値で加える。
        /// 上げたときは true。版が分からない・新しすぎるときは何もしない
        /// </summary>
        public static bool Upgrade(JObject o)
        {
            if (o["version"]?.Type != JTokenType.Integer || (int)o["version"] != 2 || !(o["rules"] is JObject r)) return false;
            if (r["summonsPerTurn"] == null) r["summonsPerTurn"] = 1;
            if (r["drawPerTurn"] == null) r["drawPerTurn"] = 1;
            if (r["firstTurnDraw"] == null) r["firstTurnDraw"] = false;
            if (r["firstTurnAttack"] == null) r["firstTurnAttack"] = false;
            o["version"] = 3;
            return true;
        }

        // ---- 書き出し ----

        public static JObject ToJson(Selector s) => new JObject
        {
            ["types"] = new JArray(s.Types),
            ["tags"] = new JArray(s.Tags),
            ["side"] = s.Side == Side.Self ? "self" : s.Side == Side.Opp ? "opp" : "both",
            ["faceUpOnly"] = s.FaceUpOnly,
            ["excludeSelf"] = s.ExcludeSelf,
        };

        static JObject ToJson(Action a) => a switch
        {
            Destroy d => new JObject { ["destroy"] = new JObject { ["target"] = ToJson(d.Target) } },
            Bounce b => new JObject { ["bounce"] = new JObject { ["target"] = ToJson(b.Target) } },
            DrawCards d => new JObject { ["draw"] = new JObject { ["count"] = d.Count } },
            Damage d => new JObject { ["damage"] = new JObject { ["amount"] = d.Amount } },
            Heal h => new JObject { ["heal"] = new JObject { ["amount"] = h.Amount } },
            _ => throw new ArgumentException("未知の動き"),
        };

        static JObject ToJson(Effect e) => e switch
        {
            Activated a => new JObject { ["activated"] = new JObject { ["actions"] = new JArray(a.Actions.Select(ToJson)) } },
            Negate n => new JObject { ["negate"] = new JObject { ["target"] = ToJson(n.Target) } },
            Boost b => new JObject { ["boost"] = new JObject { ["target"] = ToJson(b.Target), ["amount"] = b.Amount } },
            _ => throw new ArgumentException("未知の効果"),
        };

        public static JObject ToJson(Card c) => new JObject
        {
            ["name"] = c.Name,
            ["type"] = c.Type,
            ["tags"] = new JArray(c.Tags),
            ["effects"] = new JArray(c.Effects.Select(ToJson)),
            ["attack"] = c.Attack,
            ["defense"] = c.Defense,
        };

        static JObject ToJson(Zone z) => new JObject
        {
            ["name"] = z.Name,
            ["count"] = z.Count,
            ["capacity"] = z.Capacity == Capacity.One ? "one" : "many",
            ["role"] = z.Role == ZoneRole.Deck ? "deck" : z.Role == ZoneRole.Grave ? "grave" : "plain",
            ["onField"] = z.OnField,
            ["admits"] = new JArray(z.Admits),
        };

        public static JObject ToJson(Rules r) => new JObject
        {
            ["cardTypes"] = new JArray(r.CardTypes),
            ["deckSize"] = r.DeckSize,
            ["handSize"] = r.HandSize,
            ["zones"] = new JArray(r.Zones.Select(ToJson)),
            ["life"] = r.Life,
            ["fighters"] = new JArray(r.Fighters),
            ["summonsPerTurn"] = r.SummonsPerTurn,
            ["drawPerTurn"] = r.DrawPerTurn,
            ["firstTurnDraw"] = r.FirstTurnDraw,
            ["firstTurnAttack"] = r.FirstTurnAttack,
        };

        public static JObject ToJson(Game g) => new JObject
        {
            ["version"] = g.Version,
            ["rules"] = ToJson(g.Rules),
            ["cards"] = new JArray(g.Cards.Select(ToJson)),
        };
    }
}
