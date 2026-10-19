// テストプレイの山札を作る（エディタ用。Lean 側に対応なし）。
using System;
using System.Collections.Generic;
using System.Linq;

namespace CardGen
{
    public static class DeckBuilder
    {
        /// <summary>タップで出せるマナの色（2色から選べるなら、そのどれも）</summary>
        static List<string> Colors(Card c) => c.ManaChoice.Count > 0 ? c.ManaChoice : new List<string> { c.ManaColor };

        /// <summary>
        /// カードの一覧からデッキの枚数の山札を作る。マナを出すカード（土地）とそれ以外があれば、4割ほどを土地にし、
        /// 土地はほかのカードの色のコストの多さに合わせて選ぶ（色が合わずに出せないことを減らす）。
        /// 土地とそれ以外は、山札全体にむらなく散らして混ぜる（最初の手札にも土地が来るように）
        /// </summary>
        public static List<Card> Make(Game game, Random rng)
        {
            var n = game.Rules.DeckSize;
            var lands = game.Cards.Where(c => c.Mana > 0).ToList();
            var others = game.Cards.Where(c => c.Mana == 0).ToList();
            List<Card> Shuffle(List<Card> l)
            {
                for (int i = l.Count - 1; i > 0; i--)
                {
                    int j = rng.Next(i + 1);
                    (l[i], l[j]) = (l[j], l[i]);
                }
                return l;
            }
            if (game.Cards.Count == 0) return new List<Card>();
            if (lands.Count == 0 || others.Count == 0)
                return Shuffle(Enumerable.Range(0, n).Select(i => game.Cards[i % game.Cards.Count]).ToList());

            var nl = n * 2 / 5;
            var rest = Shuffle(Enumerable.Range(0, n - nl).Select(i => others[i % others.Count]).ToList());
            // 色のコストの多さ（山札に入るカードで数える）。色の決まったコストがなければ、土地を順に入れる
            var demand = rest.SelectMany(c => c.ColorCost).GroupBy(x => x).ToDictionary(g => g.Key, g => (double)g.Count());
            var supply = new Dictionary<string, int>();
            var pickedLands = new List<Card>();
            for (int i = 0; i < nl; i++)
            {
                Card best = lands[i % lands.Count];
                if (demand.Count > 0)
                {
                    // 土地の価値は、出せる色のうち一番足りない色で決める（2色の土地ばかりにならないように）
                    double Score(Card c) => Colors(c).Max(col =>
                        demand.TryGetValue(col, out var d) ? d / (1 + (supply.TryGetValue(col, out var s) ? s : 0)) : 0);
                    best = lands.OrderByDescending(Score).ThenBy(c => pickedLands.Count(x => x == c)).First();
                }
                pickedLands.Add(best);
                foreach (var col in Colors(best)) supply[col] = (supply.TryGetValue(col, out var s) ? s : 0) + 1;
            }
            Shuffle(pickedLands);
            // むらなく散らす：先頭から i 枚目までに、だいたい i × 土地の割合の土地が入るようにする
            var deck = new List<Card>();
            int li = 0, oi = 0;
            for (int i = 0; i < n; i++)
            {
                var want = (int)Math.Round((i + 1) * (double)nl / n);
                if (li < pickedLands.Count && (li < want || oi >= rest.Count)) deck.Add(pickedLands[li++]);
                else deck.Add(rest[oi++]);
            }
            return deck;
        }
    }
}
