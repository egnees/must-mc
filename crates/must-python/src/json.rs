//! Small, strict JSON codec for the bounded worker protocol (no external dependencies).
use crate::{Error, ErrorKind};
use std::collections::BTreeMap;

#[derive(Clone, Debug, PartialEq)]
pub(crate) enum Json {
    Null,
    Bool(bool),
    Number(String),
    String(String),
    Array(Vec<Json>),
    Object(BTreeMap<String, Json>),
}

impl Json {
    pub(crate) fn string(&self) -> Result<&str, Error> {
        match self {
            Self::String(s) => Ok(s),
            _ => Err(invalid("expected string")),
        }
    }
    pub(crate) fn field(&self, key: &str) -> Result<&Self, Error> {
        match self {
            Self::Object(o) => o.get(key).ok_or_else(|| invalid("missing field")),
            _ => Err(invalid("expected object")),
        }
    }
    pub(crate) fn array(&self) -> Result<&[Self], Error> {
        match self {
            Self::Array(a) => Ok(a),
            _ => Err(invalid("expected array")),
        }
    }
    pub(crate) fn number(&self) -> Result<&str, Error> {
        match self {
            Self::Number(n) => Ok(n),
            _ => Err(invalid("expected number")),
        }
    }
}

fn invalid(reason: &str) -> Error {
    Error::new(ErrorKind::Execution, format!("invalid JSON: {reason}"))
}

pub(crate) fn quote(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            '\u{0008}' => out.push_str("\\b"),
            '\u{000c}' => out.push_str("\\f"),
            c if c < ' ' => {
                use std::fmt::Write;
                let _ = write!(out, "\\u{:04x}", c as u32);
            }
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

pub(crate) fn parse(input: &str) -> Result<Json, Error> {
    let mut p = Parser {
        input: input.as_bytes(),
        pos: 0,
    };
    let value = p.value(0)?;
    p.ws();
    if p.pos != p.input.len() {
        return Err(invalid("trailing data"));
    }
    Ok(value)
}

struct Parser<'a> {
    input: &'a [u8],
    pos: usize,
}
impl Parser<'_> {
    fn ws(&mut self) {
        while self
            .input
            .get(self.pos)
            .is_some_and(|c| b" \n\r\t".contains(c))
        {
            self.pos += 1;
        }
    }
    fn byte(&mut self, c: u8) -> Result<(), Error> {
        if self.input.get(self.pos) != Some(&c) {
            return Err(invalid("unexpected character"));
        }
        self.pos += 1;
        Ok(())
    }
    fn value(&mut self, depth: usize) -> Result<Json, Error> {
        if depth > 128 {
            return Err(invalid("nesting limit exceeded"));
        }
        self.ws();
        match self.input.get(self.pos) {
            Some(b'"') => self.string().map(Json::String),
            Some(b'[') => {
                self.pos += 1;
                self.ws();
                let mut values = Vec::new();
                if self.input.get(self.pos) != Some(&b']') {
                    loop {
                        values.push(self.value(depth + 1)?);
                        self.ws();
                        if self.input.get(self.pos) == Some(&b']') {
                            break;
                        }
                        self.byte(b',')?;
                    }
                }
                self.byte(b']')?;
                Ok(Json::Array(values))
            }
            Some(b'{') => {
                self.pos += 1;
                self.ws();
                let mut values = BTreeMap::new();
                if self.input.get(self.pos) != Some(&b'}') {
                    loop {
                        self.ws();
                        let key = self.string()?;
                        self.ws();
                        self.byte(b':')?;
                        values.insert(key, self.value(depth + 1)?);
                        self.ws();
                        if self.input.get(self.pos) == Some(&b'}') {
                            break;
                        }
                        self.byte(b',')?;
                    }
                }
                self.byte(b'}')?;
                Ok(Json::Object(values))
            }
            Some(b'n') => {
                self.literal(b"null")?;
                Ok(Json::Null)
            }
            Some(b't') => {
                self.literal(b"true")?;
                Ok(Json::Bool(true))
            }
            Some(b'f') => {
                self.literal(b"false")?;
                Ok(Json::Bool(false))
            }
            Some(b'-' | b'0'..=b'9') => self.number().map(Json::Number),
            _ => Err(invalid("expected value")),
        }
    }
    fn literal(&mut self, value: &[u8]) -> Result<(), Error> {
        if self.input.get(self.pos..self.pos + value.len()) != Some(value) {
            return Err(invalid("invalid literal"));
        }
        self.pos += value.len();
        Ok(())
    }
    fn hex(&mut self) -> Result<u32, Error> {
        let bytes = self
            .input
            .get(self.pos..self.pos + 4)
            .ok_or_else(|| invalid("short unicode escape"))?;
        let s = std::str::from_utf8(bytes).map_err(|_| invalid("unicode escape"))?;
        let n = u32::from_str_radix(s, 16).map_err(|_| invalid("unicode escape"))?;
        self.pos += 4;
        Ok(n)
    }
    fn string(&mut self) -> Result<String, Error> {
        self.byte(b'"')?;
        let mut out = Vec::new();
        loop {
            let c = *self
                .input
                .get(self.pos)
                .ok_or_else(|| invalid("unterminated string"))?;
            self.pos += 1;
            match c {
                b'"' => return String::from_utf8(out).map_err(|_| invalid("invalid UTF-8")),
                0..=31 => return Err(invalid("control character in string")),
                b'\\' => {
                    let e = *self
                        .input
                        .get(self.pos)
                        .ok_or_else(|| invalid("missing escape"))?;
                    self.pos += 1;
                    match e {
                        b'"' | b'\\' | b'/' => out.push(e),
                        b'b' => out.push(8),
                        b'f' => out.push(12),
                        b'n' => out.push(10),
                        b'r' => out.push(13),
                        b't' => out.push(9),
                        b'u' => {
                            let mut n = self.hex()?;
                            if (0xd800..=0xdbff).contains(&n) {
                                self.byte(b'\\')?;
                                self.byte(b'u')?;
                                let low = self.hex()?;
                                if !(0xdc00..=0xdfff).contains(&low) {
                                    return Err(invalid("invalid surrogate pair"));
                                }
                                n = 0x10000 + ((n - 0xd800) << 10) + low - 0xdc00;
                            }
                            let c = char::from_u32(n)
                                .ok_or_else(|| invalid("invalid unicode scalar"))?;
                            let mut buf = [0; 4];
                            out.extend_from_slice(c.encode_utf8(&mut buf).as_bytes());
                        }
                        _ => return Err(invalid("invalid escape")),
                    }
                }
                c => out.push(c),
            }
        }
    }
    fn number(&mut self) -> Result<String, Error> {
        let start = self.pos;
        if self.input.get(self.pos) == Some(&b'-') {
            self.pos += 1;
        }
        if self.input.get(self.pos) == Some(&b'0') {
            self.pos += 1;
        } else {
            self.digits()?;
        }
        if self.input.get(self.pos) == Some(&b'.') {
            self.pos += 1;
            self.digits()?;
        }
        if matches!(self.input.get(self.pos), Some(b'e' | b'E')) {
            self.pos += 1;
            if matches!(self.input.get(self.pos), Some(b'+' | b'-')) {
                self.pos += 1;
            }
            self.digits()?;
        }
        Ok(std::str::from_utf8(&self.input[start..self.pos])
            .map_err(|_| invalid("number"))?
            .to_owned())
    }
    fn digits(&mut self) -> Result<(), Error> {
        let start = self.pos;
        while self.input.get(self.pos).is_some_and(u8::is_ascii_digit) {
            self.pos += 1;
        }
        if start == self.pos {
            return Err(invalid("expected digit"));
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn unicode_and_strict_syntax() {
        assert_eq!(
            parse(r#""\ud83d\ude80""#).unwrap(),
            Json::String("🚀".into())
        );
        for input in ["01", "-", "[1,]", "{\"a\":1,}", "NaN", "1.", r#""\ud800""#] {
            assert!(parse(input).is_err(), "{input}");
        }
        let s = "Привет\n\t\0🚀\\\"";
        assert_eq!(parse(&quote(s)).unwrap().string().unwrap(), s);
    }
}
