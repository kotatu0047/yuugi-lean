// 検査ツール（lake exe cardgen）の報告（CardGen/Report.lean と同じ形）。
using System.Collections.Generic;
using System.Linq;
using Newtonsoft.Json.Linq;

namespace CardGen
{
    public sealed class ClaimOut
    {
        public string Text;
        public List<string> Grounds;
        public string Status;
        public string Theorem;
    }

    public sealed class SideCard
    {
        public string Card;
        public string Side;
    }

    public sealed class GroupOut
    {
        public List<string> Cards;
        public string Status;
        public string Message;
        public List<SideCard> Board;
    }

    public sealed class NegOut
    {
        public string Status;
        public string Message;
        public List<List<string>> Edges;
        public List<GroupOut> Groups;
        public string Theorem;
    }

    public sealed class Report
    {
        public bool Ok;
        public List<string> Errors;
        public List<ClaimOut> Claims;
        public NegOut Negation;

        static List<string> Strs(JToken t) => t?.Select(x => (string)x).ToList() ?? new List<string>();

        public static Report Parse(string json)
        {
            var o = JObject.Parse(json);
            var n = o["negation"];
            return new Report
            {
                Ok = (bool)o["ok"],
                Errors = Strs(o["errors"]),
                Claims = o["claims"].Select(c => new ClaimOut
                {
                    Text = (string)c["text"],
                    Grounds = Strs(c["grounds"]),
                    Status = (string)c["status"],
                    Theorem = (string)c["theorem"],
                }).ToList(),
                Negation = n == null || n.Type == JTokenType.Null ? null : new NegOut
                {
                    Status = (string)n["status"],
                    Message = (string)n["message"],
                    Edges = n["edges"].Select(Strs).ToList(),
                    Groups = n["groups"].Select(g => new GroupOut
                    {
                        Cards = Strs(g["cards"]),
                        Status = (string)g["status"],
                        Message = (string)g["message"],
                        Board = g["board"].Select(b => new SideCard { Card = (string)b["card"], Side = (string)b["side"] }).ToList(),
                    }).ToList(),
                    Theorem = n["theorem"]?.Type == JTokenType.String ? (string)n["theorem"] : null,
                },
            };
        }

        public static string StatusLabel(string status) => status switch
        {
            "proved" => "証明済み",
            "counterexample" => "反例あり",
            "choice" => "プレイヤーの選択",
            _ => "未確定",
        };
    }
}
