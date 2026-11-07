//! scholar_zkpopk.canonical: json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True).

use num_bigint::BigInt;
use std::collections::BTreeMap;

/// A JSON value as the harness builds them (tuples are lists). No floats.
#[derive(Clone, Debug, PartialEq)]
pub enum Json {
    Null,
    Bool(bool),
    Int(BigInt),
    Str(String),
    List(Vec<Json>),
    Map(BTreeMap<String, Json>),
}

impl Json {
    pub fn s(x: &str) -> Json {
        Json::Str(x.to_string())
    }
    pub fn i(x: i64) -> Json {
        Json::Int(BigInt::from(x))
    }
    pub fn list(v: Vec<Json>) -> Json {
        Json::List(v)
    }

    pub fn canonical(&self) -> Vec<u8> {
        let mut out = Vec::new();
        self.write(&mut out);
        out
    }

    pub fn write(&self, out: &mut Vec<u8>) {
        match self {
            Json::Null => out.extend_from_slice(b"null"),
            Json::Bool(b) => out.extend_from_slice(if *b { b"true" } else { b"false" }),
            Json::Int(x) => out.extend_from_slice(x.to_string().as_bytes()),
            Json::Str(s) => write_str(s, out),
            Json::List(v) => {
                out.push(b'[');
                for (i, x) in v.iter().enumerate() {
                    if i > 0 {
                        out.push(b',');
                    }
                    x.write(out);
                }
                out.push(b']');
            }
            Json::Map(m) => {
                // Python sorts str keys by code point; BTreeMap<String> orders by UTF-8 bytes, the same order.
                out.push(b'{');
                for (i, (k, v)) in m.iter().enumerate() {
                    if i > 0 {
                        out.push(b',');
                    }
                    write_str(k, out);
                    out.push(b':');
                    v.write(out);
                }
                out.push(b'}');
            }
        }
    }

    /// From serde_json (integers only; floats refused).
    pub fn from_serde(v: &serde_json::Value) -> Result<Json, String> {
        Ok(match v {
            serde_json::Value::Null => Json::Null,
            serde_json::Value::Bool(b) => Json::Bool(*b),
            serde_json::Value::Number(n) => {
                if let Some(i) = n.as_i64() {
                    Json::i(i)
                } else if let Some(u) = n.as_u64() {
                    Json::Int(BigInt::from(u))
                } else {
                    return Err("float in canonical JSON".into());
                }
            }
            serde_json::Value::String(s) => Json::Str(s.clone()),
            serde_json::Value::Array(a) => Json::List(a.iter().map(Json::from_serde).collect::<Result<_, _>>()?),
            serde_json::Value::Object(o) => {
                Json::Map(o.iter().map(|(k, v)| Ok((k.clone(), Json::from_serde(v)?))).collect::<Result<_, String>>()?)
            }
        })
    }
}

fn write_str(s: &str, out: &mut Vec<u8>) {
    out.push(b'"');
    for ch in s.chars() {
        match ch {
            '"' => out.extend_from_slice(b"\\\""),
            '\\' => out.extend_from_slice(b"\\\\"),
            '\n' => out.extend_from_slice(b"\\n"),
            '\r' => out.extend_from_slice(b"\\r"),
            '\t' => out.extend_from_slice(b"\\t"),
            '\u{8}' => out.extend_from_slice(b"\\b"),
            '\u{c}' => out.extend_from_slice(b"\\f"),
            ' '..='~' => out.push(ch as u8),
            _ => {
                let mut buf = [0u16; 2];
                for u in ch.encode_utf16(&mut buf) {
                    out.extend_from_slice(format!("\\u{:04x}", u).as_bytes());
                }
            }
        }
    }
    out.push(b'"');
}
