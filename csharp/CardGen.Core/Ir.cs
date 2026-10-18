// 中間表現（CardGen/IR.lean と同じ形）。
// Unity でも使えるように .NET Standard 2.1 と C# 9 の範囲で書く。
using System.Collections.Generic;
using System.Linq;

namespace CardGen
{
    /// <summary>マスの容量</summary>
    public enum Capacity { One, Many }

    /// <summary>ゾーンの役割</summary>
    public enum ZoneRole { Deck, Grave, Plain }

    /// <summary>効果の持ち主から見た陣営</summary>
    public enum Side { Self, Opp, Both }

    /// <summary>ゾーンの定義（1人分）</summary>
    public sealed class Zone
    {
        public string Name = "";
        public int Count;
        public Capacity Capacity;
        public ZoneRole Role;
        public bool OnField;
        public List<string> Admits = new List<string>();
    }

    /// <summary>ゲームのルール</summary>
    public sealed class Rules
    {
        public List<string> CardTypes = new List<string>();
        public int DeckSize;
        public int HandSize;
        public List<Zone> Zones = new List<Zone>();
        /// <summary>初期ライフ</summary>
        public int Life;
        /// <summary>戦闘できる（攻撃する・攻撃される）カードの種類。空なら戦闘はない</summary>
        public List<string> Fighters = new List<string>();
        /// <summary>1ターンに置ける、戦闘できる種類のカードの枚数（通常召喚の回数）。0 なら制限なし</summary>
        public int SummonsPerTurn = 1;
        /// <summary>ターンの最初に引く枚数</summary>
        public int DrawPerTurn = 1;
        /// <summary>先攻の最初のターンにも引くか</summary>
        public bool FirstTurnDraw;
        /// <summary>先攻の最初のターンにも攻撃できるか</summary>
        public bool FirstTurnAttack;

        /// <summary>i 番目のゾーンが「フィールド上」に数えるゾーンか（Rules.onFieldZone）</summary>
        public bool OnFieldZone(int i) =>
            i >= 0 && i < Zones.Count && Zones[i].Role == ZoneRole.Plain && Zones[i].OnField;
    }

    /// <summary>範囲を判定するときに見る、フィールド上のカード1枚の情報（効果の持ち主から見たもの）</summary>
    public readonly struct View
    {
        public readonly string Type;
        public readonly IReadOnlyList<string> Tags;
        public readonly bool Mine;
        public readonly bool FaceUp;
        public readonly bool IsSelf;

        public View(string type, IReadOnlyList<string> tags, bool mine, bool faceUp, bool isSelf)
        {
            Type = type; Tags = tags; Mine = mine; FaceUp = faceUp; IsSelf = isSelf;
        }
    }

    /// <summary>範囲の指定</summary>
    public sealed class Selector
    {
        public List<string> Types = new List<string>();
        public List<string> Tags = new List<string>();
        public Side Side;
        public bool FaceUpOnly;
        public bool ExcludeSelf;

        static bool SideMatches(Side side, bool mine) =>
            side == Side.Self ? mine : side == Side.Opp ? !mine : true;

        /// <summary>Selector.matches</summary>
        public bool Matches(View v) =>
            Types.Contains(v.Type) && Tags.All(t => v.Tags.Contains(t)) && SideMatches(Side, v.Mine) &&
            (!FaceUpOnly || v.FaceUp) && !(ExcludeSelf && v.IsSelf);
    }

    /// <summary>効果が解決したときの動き</summary>
    public abstract class Action { }

    /// <summary>範囲に合うカードをすべて破壊し、持ち主の墓地へ送る</summary>
    public sealed class Destroy : Action
    {
        public Selector Target;
        public Destroy(Selector target) { Target = target; }
    }

    /// <summary>範囲に合うカードをすべて持ち主の手札に戻す</summary>
    public sealed class Bounce : Action
    {
        public Selector Target;
        public Bounce(Selector target) { Target = target; }
    }

    /// <summary>発動したプレイヤーがデッキからカードを Count 枚引く（足りなければある分だけ）</summary>
    public sealed class DrawCards : Action
    {
        public int Count;
        public DrawCards(int count) { Count = count; }
    }

    /// <summary>相手に Amount のダメージを与える</summary>
    public sealed class Damage : Action
    {
        public int Amount;
        public Damage(int amount) { Amount = amount; }
    }

    /// <summary>発動したプレイヤーのライフを Amount 回復する</summary>
    public sealed class Heal : Action
    {
        public int Amount;
        public Heal(int amount) { Amount = amount; }
    }

    /// <summary>カードの効果</summary>
    public abstract class Effect { }

    /// <summary>発動し、解決したときに動きを順に行う</summary>
    public sealed class Activated : Effect
    {
        public List<Action> Actions;
        public Activated(List<Action> actions) { Actions = actions; }
    }

    /// <summary>表側表示でフィールド上に存在する限り、範囲に合うカードの効果を無効にする</summary>
    public sealed class Negate : Effect
    {
        public Selector Target;
        public Negate(Selector target) { Target = target; }
    }

    /// <summary>表側表示でフィールド上に存在する限り、範囲に合うカードの攻撃力を Amount 変える（負なら下げる）</summary>
    public sealed class Boost : Effect
    {
        public Selector Target;
        public int Amount;
        public Boost(Selector target, int amount) { Target = target; Amount = amount; }
    }

    /// <summary>カードの定義</summary>
    public sealed class Card
    {
        public string Name = "";
        public string Type = "";
        public List<string> Tags = new List<string>();
        public List<Effect> Effects = new List<Effect>();
        public int Attack;
        public int Defense;
    }

    /// <summary>エディタが出力する中間表現の全体</summary>
    public sealed class Game
    {
        public const int CurrentVersion = 3;
        public int Version = CurrentVersion;
        public Rules Rules = new Rules();
        public List<Card> Cards = new List<Card>();
    }
}
