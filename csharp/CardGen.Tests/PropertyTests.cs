// Lean で証明した性質（盤面の制約・マナの収支・優先権・記録の整合など）が、C# の対戦エンジンでも成り立つかを、
// MTG 風と遊戯王風の見本で乱択の対戦をたくさん進めて確かめる（差分テストを補う）。
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using CardGen;
using Xunit;

public class PropertyTests
{
    static Game Load(string file) => IrJson.ParseGame(File.ReadAllText(Path.Combine(AppContext.BaseDirectory, file)));

    /// <summary>今できる動きの候補（Lean の Vectors.candidates と同じ考え方）</summary>
    static List<TChoice> Candidates(Rules r, Match m)
    {
        var l = new List<TChoice>();
        var tp = m.Turn.Tp;
        void Places(bool p, List<string> pool, bool cast)
        {
            var hand = m.G.Get(p).Hand;
            for (int h = 0; h < hand.Count; h++)
                for (int z = 0; z < r.Zones.Count; z++)
                {
                    if (r.Zones[z].Role != ZoneRole.Plain || !r.Zones[z].Admits.Contains(hand[h].Type)) continue;
                    var pay = TurnInfo.AutoPay(hand[h], pool) ?? new List<string>();
                    var cell = m.G.FreeCell(r, p, z);
                    l.Add(cast ? TChoice.Cast(h, z, cell, true, pay) : TChoice.Place(h, z, cell, true, pay));
                }
        }
        Places(tp, m.Turn.Pool, false);
        Places(!tp, m.Turn.OppPool, true);
        foreach (var (p, opp) in new[] { (tp, false), (!tp, true) })
        {
            var f = m.G.Get(p).Field;
            for (int k = 0; k < f.Count; k++)
                foreach (var c in f[k].Card.ManaChoice.Count > 0 ? f[k].Card.ManaChoice : new List<string> { "" })
                    l.Add(opp ? TChoice.OppTap(k, c) : TChoice.Tap(k, c));
        }
        for (int k = 0; k < m.G.Get(tp).Field.Count; k++) l.Add(TChoice.Attack(k, null, new List<(bool, int)>()));
        var o = m.G.Get(!tp).Field;
        l.Add(TChoice.Block(new List<(int, int)>(), new List<(bool, int)>()));
        for (int j = 0; j < o.Count; j++)
            for (int a = 0; a < m.Turn.Attackers.Count; a++)
                l.Add(TChoice.Block(new List<(int, int)> { (j, a) }, new List<(bool, int)>()));
        var pos = new List<(bool, int)?> { null };
        foreach (var q in new[] { true, false })
            for (int i = 0; i < m.G.Get(q).Field.Count; i++) pos.Add((q, i));
        foreach (var q in new[] { true, false })
            for (int k = 0; k < m.G.Get(q).Field.Count; k++)
                foreach (var t in pos) l.Add(TChoice.Resolve(q, k, 0, true, null, t));
        for (int i = 0; i < m.Turn.Pending.Count; i++) { l.Add(TChoice.Trigger(i, false, true)); l.Add(TChoice.Trigger(i, true, true)); }
        for (int h = 0; h < m.G.Get(tp).Hand.Count; h++) l.Add(TChoice.Discard(h));
        l.Add(TChoice.Pass());
        l.Add(TChoice.EndTurn());
        return l;
    }

    static int CountOf(IEnumerable<Slot> l, Slot s) => l.Count(x => x.SameBase(s));

    /// <summary>記録 rec が、フィールド field の一部（同じカードの枚数も含めて）</summary>
    static bool BagLe(List<Slot> rec, List<Slot> field) => rec.All(a => CountOf(rec, a) <= CountOf(field, a));

    static void CheckInvariants(Rules r, Match m, string where, List<Card> cards = null)
    {
        var t = m.Turn;
        // マナの色（TReachable.mana_from）：持っているマナは、マナを出すカードが出せる色だけ
        if (cards != null)
        {
            var colors = cards.Where(c => c.Mana > 0).SelectMany(c => c.ManaChoice.Count > 0 ? c.ManaChoice : new List<string> { c.ManaColor });
            Assert.True(t.Pool.Concat(t.OppPool).All(colors.Contains), $"{where}：マナの色");
        }
        // 待ちにあるのは、どれもカードの誘発する効果（TReachable.pending_triggered）
        Assert.True(t.Pending.All(e => e.Eff >= 0 && e.Eff < e.Card.Effects.Count && e.Card.Effects[e.Eff] is Triggered),
            $"{where}：待ちの効果");
        // 盤面の制約（Lean の Inv）
        Assert.True(m.G.Violations(r).Count == 0, $"{where}：盤面の制約 {string.Join("、", m.G.Violations(r))}");
        // マナの収支（TReachable.mana_balance）
        Assert.True(t.Pool.Count + t.OppPool.Count + t.Spent == t.Made, $"{where}：マナの収支");
        // パスの回数（TReachable.passes_le）
        Assert.InRange(t.Passes, 0, 2);
        // 記録の整合（TReachable.fits・stack_fits）
        var mine = m.G.Get(t.Tp).Field;
        var opp = m.G.Get(!t.Tp).Field;
        Assert.True(BagLe(t.Attacked, mine) && BagLe(t.Entered, mine) && BagLe(t.Tapped, mine) && BagLe(t.Attackers, mine),
            $"{where}：ターンプレイヤーの記録");
        Assert.True(BagLe(t.OppTapped, opp) && BagLe(t.Blocked, opp), $"{where}：相手の記録");
        Assert.True(t.Stack.All(e => m.G.Get(e.player).Field.Any(x => x.SameBase(e.slot))), $"{where}：スタック");
        // 種類ごとの上限（TReachable.placed_le）・召喚の上限（summons_le）
        foreach (var lim in r.PlaceLimits) Assert.True(t.Placed.Count(lim.Types.Contains) <= lim.Count, $"{where}：種類ごとの上限");
        if (r.SummonsPerTurn != 0) Assert.True(t.Summons <= r.SummonsPerTurn, $"{where}：召喚の上限");
        // カードの総数（★：カードの総数は常にデッキの枚数×2）
        var total = new[] { m.G.P1, m.G.P2 }.Sum(s => s.Deck.Count + s.Hand.Count + s.Grave.Count + s.Field.Count);
        Assert.Equal(2 * r.DeckSize, total);
    }

    static List<string> SortedNames(IEnumerable<Card> cs) => cs.Select(c => c.Name).OrderBy(x => x, StringComparer.Ordinal).ToList();

    /// <summary>1人分の状態にあるカード（デッキ・手札・墓地・フィールド）</summary>
    static IEnumerable<Card> AllCards(PState s) => s.Deck.Concat(s.Hand).Concat(s.Grave).Concat(s.Field.Select(x => x.Card));

    /// <summary>
    /// カードの流れ（Flow.lean の Match.step?_flow）：動きの前 a と後 b で、カードは並べ替えただけ・デッキは上から減るだけ・
    /// 墓地は後ろに加わるだけ
    /// </summary>
    static void CheckFlow(PState a, PState b, string where)
    {
        Assert.Equal(SortedNames(AllCards(a)), SortedNames(AllCards(b)));
        var da = a.Deck.Select(c => c.Name).ToList();
        var db = b.Deck.Select(c => c.Name).ToList();
        Assert.True(db.Count <= da.Count && da.Skip(da.Count - db.Count).SequenceEqual(db), $"{where}：デッキは上から減るだけ");
        var ga = a.Grave.Select(c => c.Name).ToList();
        var gb = b.Grave.Select(c => c.Name).ToList();
        Assert.True(ga.Count <= gb.Count && gb.Take(ga.Count).SequenceEqual(ga), $"{where}：墓地は後ろに加わるだけ");
    }

    static bool RaisesAtk(Card c) => c.Effects.Any(e =>
        (e is Activated a ? a.Actions : e is Triggered t ? t.Actions : new List<CardGen.Action>())
            .Any(x => x is Pump p && p.Attack > 0));

    /// <summary>
    /// ★「攻撃力の上限」（PoolClaims.lean の Reachable.atk_le）の値。攻撃力を上げる「ターンの終わりまでの変化」があれば null
    /// </summary>
    static int? AtkCap(Game game)
    {
        var r = game.Rules;
        if (r.Fighters.Count == 0 || game.Cards.Any(RaisesAtk)) return null;
        int maxAtk = game.Cards.Select(c => c.Attack).DefaultIfEmpty(0).Max();
        int boost = game.Cards.Select(c => c.Effects.OfType<Boost>().Sum(b => Math.Max(b.Amount, 0))).DefaultIfEmpty(0).Max();
        var holds = r.Zones.Where(z => z.Role == ZoneRole.Plain && z.OnField).ToList();
        int fieldCap = holds.All(z => z.Capacity == Capacity.One) ? holds.Sum(z => z.Count) : r.DeckSize;
        return maxAtk + 2 * (boost * fieldCap);
    }

    [Theory]
    [InlineData("mtg.json")]
    [InlineData("sample.json")]
    public void Random_games_keep_the_proved_properties(string file)
    {
        var game = Load(file);
        var r = game.Rules;
        int moves = 0, attacks = 0, blocks = 0, resolves = 0, triggers = 0;
        var cap = AtkCap(game);
        Assert.Equal(file == "sample.json", cap != null);   // MTG 風には巨大化があるので上限の★はない
        for (int seed = 1; seed <= 30; seed++)
        {
            var rng = new Random(seed);
            var d1 = DeckBuilder.Make(game, rng);
            var d2 = DeckBuilder.Make(game, rng);
            var m = Match.Start(r, d1, d2, seed % 2 == 0);
            CheckInvariants(r, m, $"{file} 種 {seed} 開始");
            for (int step = 0; step < 200 && !m.Over(r); step++)
            {
                var ok = Candidates(r, m).Select(ch => (ch, next: m.Step(r, ch))).Where(x => x.next != null).ToList();
                Assert.NotEmpty(ok);   // 対戦が終わっていなければ、いつも何かできる（少なくともパス）
                var busy = ok.Where(x => x.ch.Kind != TChoiceKind.Pass && x.ch.Kind != TChoiceKind.EndTurn).ToList();
                var pick = busy.Count > 0 && rng.Next(5) != 0 ? busy[rng.Next(busy.Count)] : ok[rng.Next(ok.Count)];
                var before = m;
                // 優先権（Match.step?_prio）：パス・解決・ブロック以外の動きは、優先権を持つプレイヤーのもの
                var k = pick.ch.Kind;
                if (k != TChoiceKind.Pass && k != TChoiceKind.Settle && k != TChoiceKind.Trigger && !before.Turn.AfterPasses(r, pick.ch))
                    Assert.Equal(before.Turn.Prio, pick.ch.Actor(before.Turn.Tp));
                // 待ちがあれば、その解決と状態の確認しかできない（Match.step?_pending）
                if (before.Turn.Pending.Count > 0)
                    Assert.True(k == TChoiceKind.Trigger || k == TChoiceKind.Settle, $"待ちがあるのに {k} ができた");
                m = pick.next;
                moves++;
                if (k == TChoiceKind.Attack) attacks++;
                if (k == TChoiceKind.Block) blocks++;
                if (k == TChoiceKind.Resolve) resolves++;
                if (k == TChoiceKind.Trigger) triggers++;
                CheckInvariants(r, m, $"{file} 種 {seed} {step} 手目（{k}）", game.Cards);
                // 攻撃力の上限（Reachable.atk_le）
                if (cap is int c)
                    foreach (var q in new[] { true, false })
                        for (int i = 0; i < m.G.Get(q).Field.Count; i++)
                            Assert.InRange(m.G.AtkOf(r, new List<(bool, int)>(), (q, i), m.G.Get(q).Field[i]), 0, c);
                // カードの流れ（Match.step?_flow）と、名前ごとの枚数は開始時のデッキのまま（Reachable.cards_perm）
                foreach (var q in new[] { true, false })
                {
                    CheckFlow(before.G.Get(q), m.G.Get(q), $"{file} 種 {seed} {step} 手目（{k}）");
                    Assert.Equal(SortedNames(q ? d1 : d2), SortedNames(AllCards(m.G.Get(q))));
                }
                // ターンの終わりにダメージと一時的な変化が消える（Match.endTurn_clean）
                if (k == TChoiceKind.EndTurn)
                    Assert.All(new[] { m.G.P1, m.G.P2 }.SelectMany(s => s.Field),
                        sl => Assert.True(sl.Damage == 0 && sl.AtkBonus == 0 && sl.DefBonus == 0));
            }
            // 対戦が終わったら、どの動きもできない（Match.step?_over）
            if (m.Over(r)) Assert.All(Candidates(r, m), ch => Assert.Null(m.Step(r, ch)));
        }
        Assert.True(moves > 1000 && attacks > 20 && resolves > 10 && triggers > 5,
            $"手 {moves}・攻撃 {attacks}・ブロック {blocks}・解決 {resolves}・誘発 {triggers}");
    }

    [Fact]
    public void Winner_is_decided_by_life_and_deck_out()
    {
        var game = Load("mtg.json");
        var r = game.Rules;
        var rng = new Random(3);
        var m = Match.Start(r, DeckBuilder.Make(game, rng), DeckBuilder.Make(game, rng), true);
        Assert.False(m.Over(r));
        Assert.Null(m.Winner(r));
        var lost = new Match { G = m.G.With(false, m.G.P2.With(life: 0)), Turn = m.Turn };
        Assert.True(lost.Over(r));
        Assert.Equal(true, lost.Winner(r));
        var decked = new Match { G = m.G.With(false, new PState { Hand = m.G.P2.Hand, Life = 20 }), Turn = m.Turn };
        var after = decked.Step(r, TChoice.EndTurn());
        Assert.Equal(false, after.Turn.Decked);
        Assert.Equal(true, after.Winner(r));
        Assert.Null(after.Step(r, TChoice.Pass()));
    }
}
