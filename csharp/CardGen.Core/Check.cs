// 形式の検査（CardGen/IR.lean の Game.check と同じ順番・同じ文章）。
using System.Collections.Generic;
using System.Linq;

namespace CardGen
{
    public static class Check
    {
        /// <summary>2回以上現れる要素（最初に現れた順、重複なし）</summary>
        static IEnumerable<string> Dups(List<string> l) =>
            l.Where(a => l.Count(b => b == a) > 1).Distinct();

        static IEnumerable<string> Selector(Rules r, string where, Selector s)
        {
            if (s.Types.Count == 0) yield return $"{where}：範囲のカードの種類が空です";
            foreach (var t in s.Types.Where(t => !r.CardTypes.Contains(t)))
                yield return $"{where}：範囲のカードの種類「{t}」はルールにありません";
        }

        static IEnumerable<string> Action(Rules r, string where, Action a) => a switch
        {
            Destroy d => Selector(r, $"{where}の破壊", d.Target),
            Bounce b => Selector(r, $"{where}の手札に戻す動き", b.Target),
            DrawCards d => d.Count == 0 ? new[] { $"{where}：ドローの枚数が0です" } : Enumerable.Empty<string>(),
            _ => Enumerable.Empty<string>(),
        };

        static IEnumerable<string> Effect(Rules r, string where, Effect e)
        {
            switch (e)
            {
                case Activated a:
                    if (a.Actions.Count == 0) yield return $"{where}：発動する効果に動きがありません";
                    foreach (var m in a.Actions.SelectMany(x => Action(r, where, x))) yield return m;
                    break;
                case Negate n:
                    foreach (var m in Selector(r, $"{where}の無効", n.Target)) yield return m;
                    break;
            }
        }

        static IEnumerable<string> Card(Rules r, Card c)
        {
            if (!r.CardTypes.Contains(c.Type)) yield return $"カード「{c.Name}」：種類「{c.Type}」はルールにありません";
            foreach (var m in c.Effects.SelectMany(e => Effect(r, $"カード「{c.Name}」", e))) yield return m;
        }

        static IEnumerable<string> Zone(Rules r, Zone z)
        {
            var w = $"ゾーン「{z.Name}」";
            if (z.Count == 0) yield return $"{w}：マスの数が0です";
            if (z.Admits.Count == 0) yield return $"{w}：置けるカードの種類が空です";
            foreach (var t in z.Admits.Where(t => !r.CardTypes.Contains(t)))
                yield return $"{w}：カードの種類「{t}」はルールにありません";
            var special = z.Role != ZoneRole.Plain;
            if (special && z.Capacity != Capacity.Many) yield return $"{w}：デッキや墓地の役割のゾーンは「何枚でも」にしてください";
            if (special && z.Count != 1) yield return $"{w}：デッキや墓地の役割のゾーンはマスを1つにしてください";
            if (special && z.OnField) yield return $"{w}：デッキや墓地の役割のゾーンは「フィールド上」に数えないでください";
            if (special && r.CardTypes.Any(t => !z.Admits.Contains(t)))
                yield return $"{w}：デッキや墓地の役割のゾーンには、すべての種類のカードを置けるようにしてください";
        }

        static IEnumerable<string> RulesErrors(Rules r)
        {
            if (r.CardTypes.Count == 0) yield return "ルール：カードの種類が空です";
            foreach (var t in Dups(r.CardTypes)) yield return $"ルール：カードの種類「{t}」が重複しています";
            if (r.HandSize > r.DeckSize)
                yield return $"ルール：初期手札（{r.HandSize}枚）がデッキの枚数（{r.DeckSize}枚）より多いです";
            foreach (var n in Dups(r.Zones.Select(z => z.Name).ToList())) yield return $"ルール：ゾーン「{n}」が重複しています";
            var decks = r.Zones.Count(z => z.Role == ZoneRole.Deck);
            if (decks != 1) yield return $"ルール：デッキの役割のゾーンがちょうど1つ必要です（{decks}個あります）";
            var graves = r.Zones.Count(z => z.Role == ZoneRole.Grave);
            if (graves != 1) yield return $"ルール：墓地の役割のゾーンがちょうど1つ必要です（{graves}個あります）";
            foreach (var m in r.Zones.SelectMany(z => Zone(r, z))) yield return m;
        }

        /// <summary>Game.check：問題をすべて返す。空なら中間表現として意味が通る</summary>
        public static List<string> Game(Game g)
        {
            var errors = new List<string>();
            if (g.Version != CardGen.Game.CurrentVersion)
                errors.Add($"中間表現の版 {g.Version} には対応していません（対応は {CardGen.Game.CurrentVersion}）");
            errors.AddRange(RulesErrors(g.Rules));
            errors.AddRange(Dups(g.Cards.Select(c => c.Name).ToList()).Select(n => $"カード「{n}」が重複しています"));
            errors.AddRange(g.Cards.SelectMany(c => Card(g.Rules, c)));
            return errors;
        }
    }
}
