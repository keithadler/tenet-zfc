using System.Globalization;
using System.Text;
using System.Text.RegularExpressions;

namespace TenetZfc;

/// <summary>
/// Lean names as set.mm tokens and labels (docs/milestone3.md, "Names"). A set.mm math token may hold any printable ASCII
/// character but <c>$</c>; a label only letters, digits, <c>-</c>, <c>_</c> and <c>.</c>. Lean names hold much more:
/// <c>'</c>, <c>?</c>, <c>!</c>, subscripts and other Unicode, the hygienic <c>_@</c>, numeric parts, and anything at all
/// inside «».
///
/// <see cref="Escape"/> writes a name as its components joined by <c>.</c>. A numeric component is its decimal digits. A
/// string component keeps ASCII letters, digits and <c>_</c>, and writes every other character as <c>-</c> and a code:
///
/// | character | code | example |
/// |---|---|---|
/// | <c>'</c> | <c>-q</c> | <c>List.map'</c> → <c>List.map-q</c> |
/// | <c>?</c> | <c>-Q</c> | <c>GetElem?</c> → <c>GetElem-Q</c> |
/// | <c>!</c> | <c>-B</c> | <c>get!</c> → <c>get-B</c> |
/// | <c>@</c> | <c>-a</c> | <c>_@</c> → <c>_-a</c> |
/// | <c>.</c> (inside a component, from «») | <c>-d</c> | |
/// | <c>-</c> | <c>-m</c> | |
/// | any other UTF-16 unit | <c>-u</c> and 4 hex digits | <c>a₂</c> → <c>a-u2082</c> |
/// | a character beyond U+FFFF | <c>-U</c> and 6 hex digits | |
///
/// Three kinds of string component are written whole: the empty string as <c>-z</c>; a string that a numeric component
/// or a level suffix would also print as (all digits, like <c>0</c>, or <c>u</c> and digits separated by <c>_</c>, like
/// <c>u1</c> or <c>u0_1</c>) as <c>-n</c> and the string; and <see cref="Monomorph"/>'s level suffix <c>{0,1}</c> as
/// itself. Braces and commas occur in a token only there, so <see cref="Model.LabelPart"/> can write the suffix in a label as
/// <c>u0_1</c>, which no other component prints as.
///
/// The codes avoid the letters that would make an escaped name collide with the model's own tokens and labels: no code
/// starts with <c>s</c>, <c>c</c>, <c>l</c>, <c>o</c> or <c>t</c> (the components <c>-step</c>, <c>-case</c>, <c>-lit</c>,
/// <c>-ofnum</c> and <c>lean.-tower</c>), nor with <c>e</c>, <c>i</c> or a digit (the label suffixes <c>-eq</c>,
/// <c>-iota</c>, and <c>-N</c> of a projection), and <c>--</c> never occurs. <see cref="Unescape"/> inverts it.
/// </summary>
public static class NameEscape
{
    private static readonly Regex LevelSuffix = new(@"^\{[0-9]+(,[0-9]+)*\}$", RegexOptions.CultureInvariant);
    private static readonly Regex LooksNumeric = new(@"^([0-9]+|u[0-9]+(_[0-9]+)*)$", RegexOptions.CultureInvariant);

    /// <summary>Whether a string component is a level suffix, as <see cref="Monomorph"/> names instances: c.{0,1}.</summary>
    public static bool IsLevelSuffix(string s) => LevelSuffix.IsMatch(s);

    /// <summary>The name written with only letters, digits, _ . and -, but for a level suffix's braces and commas.</summary>
    public static string Escape(Name n)
    {
        if (n.IsAnonymous)
        {
            throw new ArgumentException("the anonymous name has no token", nameof(n));
        }
        var parts = new List<string>();
        for (Name m = n; !m.IsAnonymous;)
        {
            switch (m)
            {
                case StrName s:
                    parts.Add(Component(s.Value));
                    m = s.Prefix;
                    break;
                case NumName k:
                    parts.Add(k.Value.ToString(CultureInfo.InvariantCulture));
                    m = k.Prefix;
                    break;
                default:
                    throw new ArgumentException($"unknown kind of name: {m.GetType().Name}", nameof(n));
            }
        }
        parts.Reverse();
        return string.Join('.', parts);
    }

    /// <summary>One string component, escaped.</summary>
    public static string Component(string s)
    {
        if (s.Length == 0)
        {
            return "-z";
        }
        if (IsLevelSuffix(s))
        {
            return s;
        }
        if (LooksNumeric.IsMatch(s))
        {
            return "-n" + s;
        }
        var sb = new StringBuilder(s.Length);
        for (int i = 0; i < s.Length; i++)
        {
            char ch = s[i];
            if (char.IsAsciiLetterOrDigit(ch) || ch == '_')
            {
                sb.Append(ch);
                continue;
            }
            switch (ch)
            {
                case '\'': sb.Append("-q"); break;
                case '?': sb.Append("-Q"); break;
                case '!': sb.Append("-B"); break;
                case '@': sb.Append("-a"); break;
                case '.': sb.Append("-d"); break;
                case '-': sb.Append("-m"); break;
                default:
                    if (char.IsHighSurrogate(ch) && i + 1 < s.Length && char.IsLowSurrogate(s[i + 1]))
                    {
                        sb.Append("-U").Append(char.ConvertToUtf32(ch, s[i + 1]).ToString("x6", CultureInfo.InvariantCulture));
                        i++;
                    }
                    else
                    {
                        sb.Append("-u").Append(((int)ch).ToString("x4", CultureInfo.InvariantCulture));
                    }
                    break;
            }
        }
        return sb.ToString();
    }

    /// <summary>The name an escaped string stands for; throws a System.FormatException for a string Escape never writes.</summary>
    public static Name Unescape(Terms t, string escaped)
    {
        Name n = Name.Anonymous;
        foreach (string part in escaped.Split('.'))
        {
            n = part.Length > 0 && part.All(char.IsAsciiDigit)
                ? t.Num(n, ulong.Parse(part, NumberStyles.None, CultureInfo.InvariantCulture))
                : t.Str(n, UnescapeComponent(part));
        }
        return n;
    }

    private static string UnescapeComponent(string p)
    {
        System.FormatException Bad() => new($"not an escaped name component: {p}");
        if (p == "-z")
        {
            return "";
        }
        if (IsLevelSuffix(p))
        {
            return p;
        }
        if (p.StartsWith("-n", StringComparison.Ordinal))
        {
            string rest = p[2..];
            return LooksNumeric.IsMatch(rest) ? rest : throw Bad();
        }
        var sb = new StringBuilder(p.Length);
        for (int i = 0; i < p.Length; i++)
        {
            char ch = p[i];
            if (char.IsAsciiLetterOrDigit(ch) || ch == '_')
            {
                sb.Append(ch);
                continue;
            }
            if (ch != '-' || i + 1 >= p.Length)
            {
                throw Bad();
            }
            char code = p[++i];
            switch (code)
            {
                case 'q': sb.Append('\''); break;
                case 'Q': sb.Append('?'); break;
                case 'B': sb.Append('!'); break;
                case 'a': sb.Append('@'); break;
                case 'd': sb.Append('.'); break;
                case 'm': sb.Append('-'); break;
                case 'u' or 'U':
                    {
                        int len = code == 'u' ? 4 : 6;
                        if (i + len > p.Length - 1)
                        {
                            throw Bad();
                        }
                        string hex = p.Substring(i + 1, len);
                        if (!hex.All(char.IsAsciiHexDigitLower))
                        {
                            throw Bad();
                        }
                        int cp = int.Parse(hex, NumberStyles.HexNumber, CultureInfo.InvariantCulture);
                        if (code == 'u')
                        {
                            sb.Append((char)cp);
                        }
                        else
                        {
                            sb.Append(cp is > 0xFFFF and <= 0x10FFFF ? char.ConvertFromUtf32(cp) : throw Bad());
                        }
                        i += len;
                        break;
                    }
                default:
                    throw Bad();
            }
        }
        string s = sb.ToString();
        // Escape writes these whole, so a component spelled out character by character is not one of its outputs.
        return s.Length == 0 || IsLevelSuffix(s) || LooksNumeric.IsMatch(s) || Component(s) != p ? throw Bad() : s;
    }

    /// <summary>
    /// Text safe inside a Metamath comment: printable ASCII, with no <c>$</c> (so no <c>$(</c> or <c>$)</c>). Any other
    /// character is written \u{hex}, so a comment can still show a Lean name as Lean prints it.
    /// </summary>
    public static string CommentText(string s)
    {
        if (s.All(ch => ch is >= ' ' and <= '~' and not '$'))
        {
            return s;
        }
        var sb = new StringBuilder(s.Length + 8);
        for (int i = 0; i < s.Length; i++)
        {
            char ch = s[i];
            if (ch is >= ' ' and <= '~' and not '$')
            {
                sb.Append(ch);
            }
            else if (ch is '\n' or '\r' or '\t')
            {
                sb.Append(ch);
            }
            else if (char.IsHighSurrogate(ch) && i + 1 < s.Length && char.IsLowSurrogate(s[i + 1]))
            {
                sb.Append("\\u{").Append(char.ConvertToUtf32(ch, s[++i]).ToString("x", CultureInfo.InvariantCulture)).Append('}');
            }
            else
            {
                sb.Append("\\u{").Append(((int)ch).ToString("x", CultureInfo.InvariantCulture)).Append('}');
            }
        }
        return sb.ToString();
    }
}
