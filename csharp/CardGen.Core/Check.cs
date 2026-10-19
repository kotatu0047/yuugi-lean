// 形式の検査（CardGen/IR.lean の Game.check と同じ順番・同じ文章）。
using System.Collections.Generic;
using System.Linq;

namespace CardGen
{
    public static class Check
    {
        /// <summary>2回以上現れる要素（最初に現れた順、重複なし）</summary>
        static IEnumerable<T> Dups<T>(List<T> l) =>
            l.Where(a => l.Count(b => b.Equals(a)) > 1).Distinct();

        static IEnumerable<string> Selector(Rules r, string where, Selector s)
        {
            if (s.Types.Count == 0) yield return $"{where}：範囲のカードの種類が空です";
            foreach (var t in s.Types.Where(t => !r.CardTypes.Contains(t)))
                yield return $"{where}：範囲のカードの種類「{t}」はルールにありません";
            foreach (var t in r.UnknownTags(s.Tags)) yield return $"{where}：範囲のタグ「{t}」はどのタグの集合にもありません";
        }

        static IEnumerable<string> Action(Rules r, string where, Action a) => a switch
        {
            Destroy d => Selector(r, $"{where}の破壊", d.Target),
            Bounce b => Selector(r, $"{where}の手札に戻す動き", b.Target),
            DrawCards d => d.Count == 0 ? new[] { $"{where}：ドローの枚数が0です" } : Enumerable.Empty<string>(),
            Damage d => d.Amount == 0 ? new[] { $"{where}：ダメージが0です" } : Enumerable.Empty<string>(),
            Heal h => h.Amount == 0 ? new[] { $"{where}：回復する量が0です" } : Enumerable.Empty<string>(),
            Strike st => Selector(r, $"{where}のカードへのダメージ", st.Target)
                .Concat(st.Amount == 0 ? new[] { $"{where}：カードへのダメージが0です" } : new string[0])
                .Concat(st.Target.Types.Any(t => r.Fighters.Contains(t)) ? new string[0]
                    : new[] { $"{where}：カードへのダメージの範囲に、戦闘できる種類のカードがありません" }),
            Pump pu => Selector(r, $"{where}のターンの終わりまでの変化", pu.Target)
                .Concat(pu.Attack == 0 && pu.Defense == 0 ? new[] { $"{where}：ターンの終わりまでの変化が攻撃力・守備力とも0です" } : new string[0])
                .Concat(pu.Target.Types.Any(t => r.Fighters.Contains(t)) ? new string[0]
                    : new[] { $"{where}：ターンの終わりまでの変化の範囲に、戦闘できる種類のカードがありません" }),
            Counter co => Selector(r, $"{where}の打ち消し", co.Target)
                .Concat(co.Target.Types.Any(t => r.Zones.Any(z => z.Role == ZoneRole.Plain && !z.OnField && z.Admits.Contains(t))) ? new string[0]
                    : new[] { $"{where}：打ち消す範囲の種類を、「フィールド上」でないゾーンに置けません" }),
            _ => Enumerable.Empty<string>(),
        };

        static IEnumerable<string> NoTarget(string where, Selector s) =>
            s.Target ? new[] { $"{where}：永続効果の範囲では、対象を選べません" } : new string[0];

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
                    foreach (var m in NoTarget($"{where}の無効", n.Target)) yield return m;
                    if (n.Target.Near != Near.Any) yield return $"{where}：無効の範囲には、マスの関係（隣・同じ縦列）はまだ使えません";
                    break;
                case Boost b:
                    foreach (var m in Selector(r, $"{where}の攻撃力の変化", b.Target)) yield return m;
                    foreach (var m in NoTarget($"{where}の攻撃力の変化", b.Target)) yield return m;
                    if (b.Amount == 0) yield return $"{where}：攻撃力の変化が0です";
                    if (!b.Target.Types.Any(t => r.Fighters.Contains(t)))
                        yield return $"{where}：攻撃力を変える範囲に、戦闘できる種類のカードがありません";
                    break;
                case Toughen tg:
                    foreach (var m in Selector(r, $"{where}の守備力の変化", tg.Target)) yield return m;
                    foreach (var m in NoTarget($"{where}の守備力の変化", tg.Target)) yield return m;
                    if (tg.Amount == 0) yield return $"{where}：守備力の変化が0です";
                    if (!tg.Target.Types.Any(t => r.Fighters.Contains(t)))
                        yield return $"{where}：守備力を変える範囲に、戦闘できる種類のカードがありません";
                    break;
            }
        }

        static IEnumerable<string> Card(Rules r, Card c)
        {
            if (!r.CardTypes.Contains(c.Type)) yield return $"カード「{c.Name}」：種類「{c.Type}」はルールにありません";
            foreach (var t in r.UnknownTags(c.Tags)) yield return $"カード「{c.Name}」：タグ「{t}」はどのタグの集合にもありません";
            foreach (var col in c.ColorCost.Distinct().Where(x => !r.ManaColors.Contains(x)))
                yield return $"カード「{c.Name}」：コストの色「{col}」はルールのマナの色にありません";
            if (c.ManaColor != "" && !r.ManaColors.Contains(c.ManaColor))
                yield return $"カード「{c.Name}」：出るマナの色「{c.ManaColor}」はルールのマナの色にありません";
            if (c.ManaColor != "" && c.Mana == 0) yield return $"カード「{c.Name}」：マナの色があるのに、出るマナの量が0です";
            foreach (var col in c.ManaChoice.Distinct().Where(x => !r.ManaColors.Contains(x)))
                yield return $"カード「{c.Name}」：選べるマナの色「{col}」はルールのマナの色にありません";
            foreach (var col in Dups(c.ManaChoice)) yield return $"カード「{c.Name}」：選べるマナの色「{col}」が重複しています";
            if (c.ManaChoice.Count > 0 && c.ManaColor != "") yield return $"カード「{c.Name}」：マナの色と、選べるマナの色の両方があります";
            if (c.ManaChoice.Count > 0 && c.Mana == 0) yield return $"カード「{c.Name}」：選べるマナの色があるのに、出るマナの量が0です";
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
            if (special && z.Cells.Count > 0) yield return $"{w}：デッキや墓地の役割のゾーンにはマスの位置を付けないでください";
            if (z.Cells.Count > 0 && z.Cells.Count != z.Count)
                yield return $"{w}：マスの位置の数（{z.Cells.Count}）がマスの数（{z.Count}）と違います";
            foreach (var c in z.Cells.Where(c => !(c.Col < Grid.Size && c.Row < Grid.Size)))
                yield return $"{w}：マス（{c.Col}, {c.Row}）が盤面（{Grid.Size}×{Grid.Size}）の外です";
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
            foreach (var c in Dups(r.AllCells())) yield return $"ルール：マス（{c.Col}, {c.Row}）が重なっています（相手の側のマスも含む）";
            foreach (var t in r.Fighters.Where(t => !r.CardTypes.Contains(t)))
                yield return $"ルール：戦闘できる種類「{t}」はカードの種類にありません";
            if (r.Fighters.Count > 0 && r.Life == 0) yield return "ルール：戦闘できる種類があるのに、初期ライフが0です";
            foreach (var col in Dups(r.ManaColors)) yield return $"ルール：マナの色「{col}」が重複しています";
            foreach (var n in Dups(r.TagSets.Select(t => t.Name).ToList())) yield return $"ルール：タグの集合「{n}」が重複しています";
            if (r.TagSets.Any(t => t.Name.Length == 0)) yield return "ルール：タグの集合の名前が空です";
            foreach (var t in r.TagSets)
                foreach (var v in Dups(t.Values)) yield return $"ルール：タグの集合「{t.Name}」で「{v}」が重複しています";
            if (r.ManaColors.Contains("")) yield return "ルール：マナの色に空の名前があります";
            foreach (var t in r.Instants.Where(t => !r.CardTypes.Contains(t)))
                yield return $"ルール：いつでも置ける種類「{t}」はカードの種類にありません";
            foreach (var l in r.PlaceLimits)
            {
                if (l.Types.Count == 0) yield return "ルール：置ける枚数の上限の、カードの種類が空です";
                foreach (var t in l.Types.Where(t => !r.CardTypes.Contains(t)))
                    yield return $"ルール：置ける枚数の上限の種類「{t}」はカードの種類にありません";
                if (l.Count == 0) yield return $"ルール：「{string.Join("・", l.Types)}」を置ける枚数の上限が0です";
            }
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
