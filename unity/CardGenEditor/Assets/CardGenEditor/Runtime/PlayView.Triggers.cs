using System.Collections.Generic;
using System.Linq;

namespace CardGen.App
{
    /// <summary>
    /// テストプレイの誘発：待ちの欄（解決する・行わない・対象を選ぶ）と、デモ用の自動の解決
    /// </summary>
    public sealed partial class PlayView
    {
        // 対象を選んでいる、待ちの誘発した効果の番号
        int? trigTargeting;

        /// <summary>待ちの効果の説明（持ち主・カード・条件・動き）</summary>
        string PendingText(Pending e) =>
            e.Card.Effects[e.Eff] is Triggered tr
                ? $"{Who(e.P)}の{e.Card.Name}：{NodeView.TriggerText(tr.On)}、{string.Join("、", tr.Actions.Select(ActionText))}" +
                  (tr.Optional ? "（行わなくてもよい）" : "")
                : $"{Who(e.P)}の{e.Card.Name}";

        /// <summary>待ちの効果 e の動き actions で、対象に選べるカードの位置（どれかの対象を選ぶ動きの範囲に合うもの）</summary>
        List<(bool, int)> TargetsForTrigger(Pending e, List<Action> actions)
        {
            var r = game.Rules;
            var l = new List<(bool, int)>();
            foreach (var q in new[] { true, false })
            {
                var f = state.Get(q).Field;
                for (int i = 0; i < f.Count; i++)
                {
                    var sl = f[i];
                    var src = new Src(e.P, e.Cell, (q, sl.Base()));
                    var hit = actions.Any(a =>
                    {
                        var sel = TargetSel(a);
                        if (sel == null || !sel.Matches(sl.ViewFor(r, q, src))) return false;
                        return a is Counter ? !r.OnFieldZone(sl.Zone)
                            : a is Strike || a is Pump ? MatchState.Fights(r, sl) : r.OnFieldZone(sl.Zone);
                    });
                    if (hit) l.Add((q, i));
                }
            }
            return l;
        }

        void DoTrigger(int i, (bool, int)? tgt)
        {
            var e = match.Turn.Pending[i];
            trigTargeting = null;
            var tname = tgt is (bool q, int k) ? $"：対象は{Who(q)}の{state.Get(q).Field[k].Card.Name}" : "";
            Do(TChoice.Trigger(i, false, true, NegList(NegationStatus(out _)), tgt), $"{Who(e.P)}：{e.Card.Name} の誘発した効果を解決{tname}");
        }

        /// <summary>待ちの欄：待ちの一覧と、解決するプレイヤーの「解決する」「行わない」（対象を選ぶ動きがあれば対象の選択）</summary>
        void PendingPanel()
        {
            var t = match.Turn;
            if (t.Pending.Count == 0) { trigTargeting = null; return; }
            Section("誘発した効果（待ち）");
            side.Add(Text($"待ちがあるうちは、その解決と状態の確認しかできません。{Who(t.PendingPlayer)}が、自分の待ちを解決する順番を選びます" +
                          "（ターンプレイヤーの待ちが先）", 11, Warn));
            for (int i = 0; i < t.Pending.Count; i++)
                side.Add(Text($"{i + 1}. {PendingText(t.Pending[i])}", 12, t.Pending[i].P == t.PendingPlayer ? Theme.Bright : Quiet));
            if (trigTargeting is int ti && ti < t.Pending.Count && t.Pending[ti].Card.Effects[t.Pending[ti].Eff] is Triggered ttr)
            {
                var e = t.Pending[ti];
                side.Add(Text($"対象を選ぶ（{e.Card.Name}）", 12, Warn, true));
                foreach (var (q, k) in TargetsForTrigger(e, ttr.Actions))
                {
                    int kk = k;
                    bool qq = q;
                    ActionButton($"{Who(q)}の{state.Get(q).Field[k].Card.Name}を対象にする", () => DoTrigger(ti, (qq, kk)));
                }
                ActionButton("対象を選ばずに解決する（対象を選ぶ動きは何も起きない）", () => DoTrigger(ti, null));
                ActionButton("やめる", () => { trigTargeting = null; Render(); });
                return;
            }
            trigTargeting = null;
            for (int i = 0; i < t.Pending.Count; i++)
            {
                var e = t.Pending[i];
                if (e.P != t.PendingPlayer || !(e.Card.Effects[e.Eff] is Triggered tr)) continue;
                int ii = i;
                var what = string.Join("、", tr.Actions.Select(ActionText));
                ActionButton($"解決する：{e.Card.Name}（{what}）", () =>
                {
                    if (tr.Actions.Any(a => TargetSel(a) != null)) { trigTargeting = ii; Render(); }
                    else DoTrigger(ii, null);
                });
                if (tr.Optional)
                    ActionButton($"行わない：{e.Card.Name}（「〜できる」効果）",
                        () => Do(TChoice.Trigger(ii, true, true), $"{Who(e.P)}：{e.Card.Name} の効果を行わない"));
            }
        }

        /// <summary>デモ用：待ちを順に解決する（対象は選ばない。行わない方は選ばない）</summary>
        void ResolvePending()
        {
            for (int guard = 0; guard < 30 && match.Turn.Pending.Count > 0; guard++)
            {
                var t = match.Turn;
                var i = t.Pending.FindIndex(x => x.P == t.PendingPlayer);
                if (i < 0) break;
                var e = t.Pending[i];
                var next = match.Step(game.Rules, TChoice.Trigger(i, false, true)) ?? match.Step(game.Rules, TChoice.Trigger(i, true, true));
                if (next == null) break;
                log.Add($"{Who(e.P)}：{e.Card.Name} の誘発した効果を解決");
                match = next;
                judge.Sync(state, game.Rules, turn);
            }
        }
    }
}
