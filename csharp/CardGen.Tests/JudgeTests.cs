// テストプレイの無効の判定（Judge）：適用された順番で結果が決まること。
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using CardGen;
using Xunit;

public class JudgeTests
{
    static readonly Game G = IrJson.ParseGame(File.ReadAllText(Path.Combine(AppContext.BaseDirectory, "sample.json")));
    static Card C(string name) => G.Cards.First(c => c.Name == name);
    static int ZoneFor(Card c) => G.Rules.Zones.FindIndex(z => z.Role == ZoneRole.Plain && z.Admits.Contains(c.Type));
    static int nextCell;
    static Slot S(string name) { var c = C(name); return new Slot(ZoneFor(c), nextCell++ % 5, c, true); }

    static MatchState Board(List<Slot> mine, List<Slot> theirs) =>
        new MatchState { P1 = new PState { Field = mine.ToList() }, P2 = new PState { Field = theirs.ToList() } };

    const string BlooD = "D－HERO Bloo－D";

    [Fact]
    public void Later_BlooD_is_negated_by_earlier_one()
    {
        var j = new Judge();
        var theirs = S(BlooD);
        j.Sync(Board(new List<Slot>(), new List<Slot> { theirs }), G.Rules, false);
        Assert.True(j.IsOn(theirs));
        // 相手の Bloo－D がいるところに、自分の Bloo－D を出す
        var mine = S(BlooD);
        j.Sync(Board(new List<Slot> { mine }, new List<Slot> { theirs }), G.Rules, true);
        Assert.Equal(Judge.Outcome.Unique, j.Result);
        Assert.True(j.IsOn(theirs));
        Assert.False(j.IsOn(mine));
        // 相手の Bloo－D がいなくなれば、自分の Bloo－D の効果が適用される
        j.Sync(Board(new List<Slot> { mine }, new List<Slot>()), G.Rules, false);
        Assert.True(j.IsOn(mine));
    }

    [Fact]
    public void Earlier_BlooD_wins_whichever_side()
    {
        var j = new Judge();
        var mine = S(BlooD);
        j.Sync(Board(new List<Slot> { mine }, new List<Slot>()), G.Rules, true);
        var theirs = S(BlooD);
        j.Sync(Board(new List<Slot> { mine }, new List<Slot> { theirs }), G.Rules, false);
        Assert.True(j.IsOn(mine));
        Assert.False(j.IsOn(theirs));
    }

    [Fact]
    public void Skill_drain_negates_monsters_placed_before_and_after()
    {
        var j = new Judge();
        var bd = S(BlooD);
        j.Sync(Board(new List<Slot>(), new List<Slot> { bd }), G.Rules, false);
        var sd = S("スキルドレイン");
        j.Sync(Board(new List<Slot> { sd }, new List<Slot> { bd }), G.Rules, true);
        Assert.True(j.IsOn(sd));
        Assert.False(j.IsOn(bd));
        var jinzo = S("人造人間－サイコ・ショッカー");
        j.Sync(Board(new List<Slot> { sd }, new List<Slot> { bd, jinzo }), G.Rules, false);
        Assert.True(j.IsOn(sd));
        Assert.False(j.IsOn(jinzo));
    }

    [Fact]
    public void Earlier_decree_wins()
    {
        var j = new Judge();
        var a = S("王宮のお触れ");
        j.Sync(Board(new List<Slot> { a }, new List<Slot>()), G.Rules, true);
        var b = S("王宮のお触れ");
        j.Sync(Board(new List<Slot> { a }, new List<Slot> { b }), G.Rules, false);
        Assert.True(j.IsOn(a));
        Assert.False(j.IsOn(b));
    }

    /// <summary>スキルドレインが場を離れ、2体の Bloo－D が同時に適用を始めるときは、ターンプレイヤーの方が先に適用されて勝つ</summary>
    [Theory]
    [InlineData(true)]
    [InlineData(false)]
    public void Turn_player_wins_when_applied_together(bool tp)
    {
        var j = new Judge();
        var mine = S(BlooD);
        var sd = S("スキルドレイン");
        var theirs = S(BlooD);
        j.Sync(Board(new List<Slot> { mine }, new List<Slot>()), G.Rules, true);
        j.Sync(Board(new List<Slot> { mine }, new List<Slot> { sd }), G.Rules, false);
        j.Sync(Board(new List<Slot> { mine }, new List<Slot> { sd, theirs }), G.Rules, false);
        Assert.False(j.IsOn(mine));
        Assert.False(j.IsOn(theirs));
        // スキルドレインが場を離れる（tp のターン）
        j.Sync(Board(new List<Slot> { mine }, new List<Slot> { theirs }), G.Rules, tp);
        Assert.Equal(Judge.Outcome.Unique, j.Result);
        Assert.Equal(tp, j.IsOn(mine));
        Assert.Equal(!tp, j.IsOn(theirs));
    }
}

public class JudgeDamageTests
{
    [Fact]
    public void Judge_keeps_the_order_when_a_card_takes_damage()
    {
        var g = IrJson.ParseGame(File.ReadAllText(Path.Combine(AppContext.BaseDirectory, "sample.json")));
        var blooD = g.Cards.First(c => c.Name == "D－HERO Bloo－D");
        var r = g.Rules;
        var theirs = new Slot(0, 0, blooD, true);
        var mine = new Slot(0, 0, blooD, true);
        var j = new Judge();
        j.Sync(new MatchState { P1 = new PState(), P2 = new PState { Field = new List<Slot> { theirs } } }, r, false);
        var board = new MatchState { P1 = new PState { Field = new List<Slot> { mine } }, P2 = new PState { Field = new List<Slot> { theirs } } };
        j.Sync(board, r, true);
        Assert.True(j.IsOn(theirs));
        Assert.False(j.IsOn(mine));
        // 相手の Bloo－D がダメージを受けても、同じカードとして順番を覚えている（自分の Bloo－D は無効のまま）
        var hurt = board.With(false, board.P2.Mark(i => 500));
        j.Sync(hurt, r, true);
        Assert.True(j.IsOn(hurt.P2.Field[0]));
        Assert.False(j.IsOn(hurt.P1.Field[0]));
    }
}
