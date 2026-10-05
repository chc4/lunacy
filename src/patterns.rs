//! Lua 5.1's string patterns, as `lstrlib.c` matches them, over bytes.

use std::ops::Range;

// Note [Patterns]
// ~~~~~~~~~~~~~~~
// A pattern matches as Lua 5.1's does, by backtracking: its items match one at
// a time from the subject's position, and a repetition tries its counts, most
// first for `*` and `+` and fewest first for `-`, until the rest of the pattern
// matches. Character classes are the C locale's. A pattern ends at a zero byte,
// as Lua 5.1's, a C string, does (`%z` matches one); a plain search, which
// isn't a pattern, uses all of its bytes.
//
// A capture is a range of the subject, or a position, `()`. A match made with
// no captures has the whole match as its only one, where its value is asked
// for, and a malformed pattern, or a capture used wrongly, is an error with
// Lua 5.1's message.

/// The most captures a pattern may have.
const MAX_CAPTURES: usize = 32;

/// A capture's length while it is open.
const CAP_UNFINISHED: isize = -1;
/// A position capture's length.
const CAP_POSITION: isize = -2;

/// The bytes that make a pattern more than a plain string.
const SPECIALS: &[u8] = b"^$*+?.([%-";

/// A capture's value: a range of the subject, or a position (1-based).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Capture {
    Bytes(Range<usize>),
    Position(usize),
}

/// The state of matching a pattern against a subject.
struct MatchState<'a> {
    src: &'a [u8],
    pat: &'a [u8],
    level: usize,
    /// Each capture's start and length (or `CAP_UNFINISHED`, `CAP_POSITION`).
    capture: [(usize, isize); MAX_CAPTURES],
}

/// A match of a pattern: the range it matched, and its captures.
pub struct Found<'m, 'a> {
    state: &'m MatchState<'a>,
    pub range: Range<usize>,
}

impl Found<'_, '_> {
    /// Capture `i`, or the whole match for capture 0 of a pattern without any.
    pub fn capture(&self, i: usize) -> Result<Capture, String> {
        self.state.capture(i, self.range.clone())
    }

    /// Its captures, or the whole match if it has none.
    pub fn captures(&self) -> Result<Vec<Capture>, String> {
        (0..self.state.level.max(1)).map(|i| self.capture(i)).collect()
    }

    /// Its pattern's captures, none if it has none.
    pub fn explicit(&self) -> Result<Vec<Capture>, String> {
        (0..self.state.level).map(|i| self.capture(i)).collect()
    }
}

/// `pat` as matched: up to a zero byte, and whether it is anchored (`^`),
/// without the anchor.
fn prepare(pat: &[u8]) -> (&[u8], bool) {
    let pat = &pat[..pat.iter().position(|&b| b == 0).unwrap_or(pat.len())];
    match pat.first() {
        Some(b'^') => (&pat[1..], true),
        _ => (pat, false),
    }
}

/// Whether `pat` has a byte that makes it a pattern, before any zero byte.
pub fn has_specials(pat: &[u8]) -> bool {
    pat.iter().take_while(|&&b| b != 0).any(|b| SPECIALS.contains(b))
}

/// Where `needle` first occurs in `haystack`: an empty one at 0.
pub fn find_plain(haystack: &[u8], needle: &[u8]) -> Option<usize> {
    if needle.is_empty() {
        return Some(0);
    }
    haystack.windows(needle.len()).position(|window| window == needle)
}

/// The first match of `pat` in `src` from `init` on, as `string.find` and
/// `string.match` search: only at `init` if anchored. `found` makes what the
/// caller wants of it.
pub fn find<T>(src: &[u8], pat: &[u8], init: usize, found: impl FnOnce(&Found) -> Result<T, String>) -> Result<Option<T>, String> {
    let (pat, anchor) = prepare(pat);
    let mut state = MatchState::new(src, pat);
    let mut s = init;
    loop {
        state.level = 0;
        if let Some(e) = state.do_match(s, 0)? {
            return found(&Found { state: &state, range: s..e }).map(Some);
        }
        if s >= src.len() || anchor {
            return Ok(None);
        }
        s += 1;
    }
}

/// The match of `pat` at `s` of `src` exactly, as `string.gmatch` tries each
/// position: its end, and what `found` makes of it.
pub fn match_at<T>(src: &[u8], pat: &[u8], s: usize, found: impl FnOnce(&Found) -> Result<T, String>) -> Result<Option<T>, String> {
    let pat = &pat[..pat.iter().position(|&b| b == 0).unwrap_or(pat.len())];
    let mut state = MatchState::new(src, pat);
    match state.do_match(s, 0)? {
        Some(e) => found(&Found { state: &state, range: s..e }).map(Some),
        None => Ok(None),
    }
}

/// `src` with up to `max` matches of `pat` replaced, as `string.gsub` makes it,
/// and how many: `replace` gives a match's replacement, or none to keep it.
pub fn gsub(src: &[u8], pat: &[u8], max: i64, mut replace: impl FnMut(&Found) -> Result<Option<Vec<u8>>, String>) -> Result<(Vec<u8>, usize), String> {
    let (pat, anchor) = prepare(pat);
    let mut state = MatchState::new(src, pat);
    let mut out = Vec::with_capacity(src.len());
    let (mut s, mut n) = (0, 0);
    while (n as i64) < max {
        state.level = 0;
        let e = state.do_match(s, 0)?;
        if let Some(e) = e {
            n += 1;
            match replace(&Found { state: &state, range: s..e })? {
                Some(replacement) => out.extend_from_slice(&replacement),
                None => out.extend_from_slice(&src[s..e]),
            }
        }
        match e {
            Some(e) if e > s => s = e,
            _ if s < src.len() => {
                out.push(src[s]);
                s += 1;
            },
            _ => break,
        }
        if anchor {
            break;
        }
    }
    out.extend_from_slice(&src[s..]);
    Ok((out, n))
}

/// Whether `c` is in the class `cl` (the letter after `%`), or is `cl` for
/// any other byte.
fn match_class(c: u8, cl: u8) -> bool {
    let res = match cl.to_ascii_lowercase() {
        b'a' => c.is_ascii_alphabetic(),
        b'c' => c < 0x20 || c == 0x7f,
        b'd' => c.is_ascii_digit(),
        b'l' => c.is_ascii_lowercase(),
        b'p' => c.is_ascii_punctuation(),
        // C's `isspace`, which has the vertical tab.
        b's' => matches!(c, b' ' | b'\t' | b'\n' | 0x0b | 0x0c | b'\r'),
        b'u' => c.is_ascii_uppercase(),
        b'w' => c.is_ascii_alphanumeric(),
        b'x' => c.is_ascii_hexdigit(),
        b'z' => c == 0,
        _ => return cl == c,
    };
    if cl.is_ascii_uppercase() { !res } else { res }
}

impl<'a> MatchState<'a> {
    fn new(src: &'a [u8], pat: &'a [u8]) -> Self {
        MatchState { src, pat, level: 0, capture: [(0, 0); MAX_CAPTURES] }
    }

    /// The pattern's byte at `p`, zero past its end.
    fn pc(&self, p: usize) -> u8 {
        self.pat.get(p).copied().unwrap_or(0)
    }

    /// The subject's byte at `s`, zero past its end.
    fn sc(&self, s: usize) -> u8 {
        self.src.get(s).copied().unwrap_or(0)
    }

    /// Where the rest of the pattern matches from `s`, the pattern from `p`:
    /// the end of the match, if it does.
    fn do_match(&mut self, mut s: usize, mut p: usize) -> Result<Option<usize>, String> {
        loop {
            match self.pc(p) {
                0 => return Ok(Some(s)),
                b'(' if self.pc(p + 1) == b')' => return self.start_capture(s, p + 2, CAP_POSITION),
                b'(' => return self.start_capture(s, p + 1, CAP_UNFINISHED),
                b')' => return self.end_capture(s, p + 1),
                b'$' if p + 1 == self.pat.len() => return Ok((s == self.src.len()).then_some(s)),
                b'%' if self.pc(p + 1) == b'b' => match self.match_balance(s, p + 2)? {
                    Some(e) => {
                        s = e;
                        p += 4;
                    },
                    None => return Ok(None),
                },
                b'%' if self.pc(p + 1) == b'f' => {
                    p += 2;
                    if self.pc(p) != b'[' {
                        return Err("missing '[' after '%f' in pattern".into());
                    }
                    let ep = self.class_end(p)?;
                    let previous = if s == 0 { 0 } else { self.src[s - 1] };
                    if self.match_bracket_class(previous, p, ep - 1) || !self.match_bracket_class(self.sc(s), p, ep - 1) {
                        return Ok(None);
                    }
                    p = ep;
                },
                b'%' if self.pc(p + 1).is_ascii_digit() => match self.match_capture(s, self.pc(p + 1))? {
                    Some(e) => {
                        s = e;
                        p += 2;
                    },
                    None => return Ok(None),
                },
                _ => {
                    let ep = self.class_end(p)?;
                    let m = s < self.src.len() && self.single_match(self.src[s], p, ep);
                    match self.pc(ep) {
                        b'?' => {
                            if m && let Some(res) = self.do_match(s + 1, ep + 1)? {
                                return Ok(Some(res));
                            }
                            p = ep + 1;
                        },
                        b'*' => return self.max_expand(s, p, ep),
                        b'+' => return if m { self.max_expand(s + 1, p, ep) } else { Ok(None) },
                        b'-' => return self.min_expand(s, p, ep),
                        _ => {
                            if !m {
                                return Ok(None);
                            }
                            s += 1;
                            p = ep;
                        },
                    }
                },
            }
        }
    }

    /// Where the single-byte item at `p` ends.
    fn class_end(&self, mut p: usize) -> Result<usize, String> {
        let c = self.pc(p);
        p += 1;
        match c {
            b'%' if self.pc(p) == 0 => Err("malformed pattern (ends with '%')".into()),
            b'%' => Ok(p + 1),
            b'[' => {
                if self.pc(p) == b'^' {
                    p += 1;
                }
                // The first byte is in the set even if it is `]`.
                loop {
                    if self.pc(p) == 0 {
                        return Err("malformed pattern (missing ']')".into());
                    }
                    let c = self.pc(p);
                    p += 1;
                    if c == b'%' && self.pc(p) != 0 {
                        p += 1;
                    }
                    if self.pc(p) == b']' {
                        return Ok(p + 1);
                    }
                }
            },
            _ => Ok(p),
        }
    }

    /// Whether `c` is in the set from `[` at `p` to `]` at `ec`.
    fn match_bracket_class(&self, c: u8, mut p: usize, ec: usize) -> bool {
        let mut sig = true;
        if self.pc(p + 1) == b'^' {
            sig = false;
            p += 1;
        }
        loop {
            p += 1;
            if p >= ec {
                return !sig;
            }
            if self.pc(p) == b'%' {
                p += 1;
                if match_class(c, self.pc(p)) {
                    return sig;
                }
            } else if self.pc(p + 1) == b'-' && p + 2 < ec {
                p += 2;
                if self.pc(p - 2) <= c && c <= self.pc(p) {
                    return sig;
                }
            } else if self.pc(p) == c {
                return sig;
            }
        }
    }

    /// Whether `c` matches the single-byte item from `p` to `ep`.
    fn single_match(&self, c: u8, p: usize, ep: usize) -> bool {
        match self.pc(p) {
            b'.' => true,
            b'%' => match_class(c, self.pc(p + 1)),
            b'[' => self.match_bracket_class(c, p, ep - 1),
            pc => pc == c,
        }
    }

    /// `%b` with its two bytes at `p`: where a balanced run from `s` ends.
    fn match_balance(&self, s: usize, p: usize) -> Result<Option<usize>, String> {
        if self.pc(p) == 0 || self.pc(p + 1) == 0 {
            return Err("unbalanced pattern".into());
        }
        if s >= self.src.len() || self.src[s] != self.pc(p) {
            return Ok(None);
        }
        let (open, close) = (self.pc(p), self.pc(p + 1));
        let mut depth = 1;
        for (at, &c) in self.src.iter().enumerate().skip(s + 1) {
            if c == close {
                depth -= 1;
                if depth == 0 {
                    return Ok(Some(at + 1));
                }
            } else if c == open {
                depth += 1;
            }
        }
        Ok(None)
    }

    /// The item from `p` to `ep` repeated as often as it matches from `s`,
    /// then fewer, until the rest of the pattern matches.
    fn max_expand(&mut self, s: usize, p: usize, ep: usize) -> Result<Option<usize>, String> {
        let mut i = 0;
        while s + i < self.src.len() && self.single_match(self.src[s + i], p, ep) {
            i += 1;
        }
        for i in (0..=i).rev() {
            if let Some(res) = self.do_match(s + i, ep + 1)? {
                return Ok(Some(res));
            }
        }
        Ok(None)
    }

    /// The item from `p` to `ep` repeated as few times as the rest of the
    /// pattern needs.
    fn min_expand(&mut self, mut s: usize, p: usize, ep: usize) -> Result<Option<usize>, String> {
        loop {
            if let Some(res) = self.do_match(s, ep + 1)? {
                return Ok(Some(res));
            }
            if s < self.src.len() && self.single_match(self.src[s], p, ep) {
                s += 1;
            } else {
                return Ok(None);
            }
        }
    }

    fn start_capture(&mut self, s: usize, p: usize, what: isize) -> Result<Option<usize>, String> {
        if self.level >= MAX_CAPTURES {
            return Err("too many captures".into());
        }
        self.capture[self.level] = (s, what);
        self.level += 1;
        let res = self.do_match(s, p)?;
        if res.is_none() {
            self.level -= 1;
        }
        Ok(res)
    }

    fn end_capture(&mut self, s: usize, p: usize) -> Result<Option<usize>, String> {
        let l = (0..self.level).rev().find(|&l| self.capture[l].1 == CAP_UNFINISHED).ok_or("invalid pattern capture")?;
        self.capture[l].1 = (s - self.capture[l].0) as isize;
        let res = self.do_match(s, p)?;
        if res.is_none() {
            self.capture[l].1 = CAP_UNFINISHED;
        }
        Ok(res)
    }

    /// A back reference, `%` and the digit `d`: where the capture's bytes
    /// matched again at `s` end.
    fn match_capture(&self, s: usize, d: u8) -> Result<Option<usize>, String> {
        let l = d as isize - b'1' as isize;
        if l < 0 || l as usize >= self.level || self.capture[l as usize].1 == CAP_UNFINISHED {
            return Err("invalid capture index".into());
        }
        let (init, len) = self.capture[l as usize];
        // A position has no bytes to match.
        if len < 0 {
            return Ok(None);
        }
        let len = len as usize;
        Ok((self.src.len() - s >= len && self.src[init..init + len] == self.src[s..s + len]).then_some(s + len))
    }

    /// Capture `i` of the match `whole`, or `whole` for capture 0 if there are
    /// none.
    fn capture(&self, i: usize, whole: Range<usize>) -> Result<Capture, String> {
        if i >= self.level {
            return if i == 0 { Ok(Capture::Bytes(whole)) } else { Err("invalid capture index".into()) };
        }
        match self.capture[i] {
            (_, CAP_UNFINISHED) => Err("unfinished capture".into()),
            (init, CAP_POSITION) => Ok(Capture::Position(init + 1)),
            (init, len) => Ok(Capture::Bytes(init..init + len as usize)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `string.find`'s range and explicit captures, as strings and positions.
    fn find_str(src: &str, pat: &str) -> Option<(usize, usize, Vec<String>)> {
        find(src.as_bytes(), pat.as_bytes(), 0, |found| {
            let captures = found.explicit()?.into_iter().map(|c| match c {
                Capture::Bytes(r) => src[r].to_string(),
                Capture::Position(p) => format!("@{p}"),
            });
            Ok((found.range.start + 1, found.range.end, captures.collect()))
        }).unwrap()
    }

    #[test]
    fn classes_and_repetitions() {
        assert_eq!(find_str("hello world", "o w"), Some((5, 7, vec![])));
        assert_eq!(find_str("  x = 42 ", "(%w+)%s*=%s*(%d+)"), Some((3, 8, vec!["x".into(), "42".into()])));
        assert_eq!(find_str("aaab", "a-b"), Some((1, 4, vec![])));
        assert_eq!(find_str("aaab", "^a?a"), Some((1, 2, vec![])));
        assert_eq!(find_str("key: value", "^(%a+):%s*(.-)$"), Some((1, 10, vec!["key".into(), "value".into()])));
        assert_eq!(find_str("a\x0bb", "a%sb"), Some((1, 3, vec![])));
    }

    #[test]
    fn sets_balance_frontier_and_back_references() {
        assert_eq!(find_str("x]y", "[]]"), Some((2, 2, vec![])));
        assert_eq!(find_str("f(a(b)c) d", "%b()"), Some((2, 8, vec![])));
        assert_eq!(find_str("THE (quick) fox", "%f[%a]%a+"), Some((1, 3, vec![])));
        assert_eq!(find_str("say 'hi' now", "(['\"])(.-)%1"), Some((5, 8, vec!["'".into(), "hi".into()])));
        assert_eq!(find_str("abc", "()b()"), Some((2, 2, vec!["@2".into(), "@3".into()])));
    }

    #[test]
    fn malformed_patterns() {
        let err = |pat: &str| find(b"abc", pat.as_bytes(), 0, |_| Ok(())).unwrap_err();
        assert_eq!(err("%"), "malformed pattern (ends with '%')");
        assert_eq!(err("[a"), "malformed pattern (missing ']')");
        assert_eq!(err("a)"), "invalid pattern capture");
        assert_eq!(err("%1"), "invalid capture index");
        assert_eq!(err("%b"), "unbalanced pattern");
        assert_eq!(err("%fa"), "missing '[' after '%f' in pattern");
    }

    #[test]
    fn substitutions() {
        let sub = |src: &str, pat: &str, max: i64| {
            let (out, n) = gsub(src.as_bytes(), pat.as_bytes(), max, |found| {
                Ok(Some(match found.capture(0)? {
                    Capture::Bytes(r) => format!("<{}>", &src[r]).into_bytes(),
                    Capture::Position(p) => p.to_string().into_bytes(),
                }))
            }).unwrap();
            (String::from_utf8(out).unwrap(), n)
        };
        assert_eq!(sub("hello world", "o", 99), ("hell<o> w<o>rld".into(), 2));
        assert_eq!(sub("abc", "", 99), ("<>a<>b<>c<>".into(), 4));
        assert_eq!(sub("abc", "x*", 2), ("<>a<>bc".into(), 2));
        assert_eq!(sub("aaa", "^a", 99), ("<a>aa".into(), 1));
    }
}
