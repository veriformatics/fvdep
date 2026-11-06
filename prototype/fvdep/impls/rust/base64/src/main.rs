//! Strict base64 adapter: modules base64.{encode,decode,encode_url,decode_url}@1.0.0.
use std::io::{self, BufRead, Write};

const STD: &[u8; 64] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
const URL: &[u8; 64] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_";

fn encode(bs: &[u8], alpha: &[u8; 64]) -> String {
    let mut out = String::with_capacity(bs.len().div_ceil(3) * 4);
    for g in bs.chunks(3) {
        let n = (g[0] as u32) << 16 | (*g.get(1).unwrap_or(&0) as u32) << 8 | *g.get(2).unwrap_or(&0) as u32;
        for k in 0..4 {
            out.push(if k <= g.len() { alpha[(n >> (18 - 6 * k) & 63) as usize] as char } else { '=' });
        }
    }
    out
}

fn decode(s: &str, alpha: &[u8; 64]) -> Option<Vec<u8>> {
    let b = s.as_bytes();
    if b.len() % 4 != 0 {
        return None;
    }
    let val = |c: u8| alpha.iter().position(|&a| a == c).map(|i| i as u32);
    let mut out = Vec::with_capacity(b.len() / 4 * 3);
    for (i, g) in b.chunks(4).enumerate() {
        let last = (i + 1) * 4 == b.len();
        let pad = if last { g.iter().rev().take_while(|&&c| c == b'=').count() } else { 0 };
        if pad > 2 {
            return None;
        }
        let mut n = 0u32;
        for &c in &g[..4 - pad] {
            n = n << 6 | val(c)?;
        }
        n <<= 6 * pad as u32;
        if pad > 0 && n & ((1 << (8 * pad)) - 1) != 0 {
            return None;
        }
        out.extend_from_slice(&n.to_be_bytes()[1..4 - pad]);
    }
    Some(out)
}

fn hex(bs: &[u8]) -> String {
    bs.iter().map(|b| format!("{b:02x}")).collect()
}

fn unhex(s: &str) -> Option<Vec<u8>> {
    if s.len() % 2 != 0 || !s.bytes().all(|c| c.is_ascii_digit() || (b'a'..=b'f').contains(&c)) {
        return None;
    }
    (0..s.len()).step_by(2).map(|i| u8::from_str_radix(&s[i..i + 2], 16).ok()).collect()
}

fn reply(r: Option<String>) -> String {
    r.map_or("err".into(), |v| format!("ok\t{v}"))
}

fn main() {
    let mut out = io::stdout().lock();
    for line in io::stdin().lock().lines() {
        let line = line.expect("stdin");
        let mut parts = line.split('\t');
        let (op, arg) = (parts.next().unwrap_or(""), parts.next().unwrap_or(""));
        let r = match op {
            "encode" => reply(unhex(arg).map(|b| encode(&b, STD))),
            "decode" => reply(decode(arg, STD).map(|b| hex(&b))),
            "encode_url" => reply(unhex(arg).map(|b| encode(&b, URL))),
            "decode_url" => reply(decode(arg, URL).map(|b| hex(&b))),
            _ => "unsupported".into(),
        };
        writeln!(out, "{r}").expect("stdout");
        out.flush().expect("stdout");
    }
}
