//! Adapter: crates.io `base64` (engines STANDARD + URL_SAFE, default config) behind the fvdep protocol.
use base64::engine::general_purpose::{STANDARD, URL_SAFE};
use base64::Engine;
use std::io::{self, BufRead, Write};

fn hex(bs: &[u8]) -> String {
    bs.iter().map(|b| format!("{b:02x}")).collect()
}

fn unhex(s: &str) -> Option<Vec<u8>> {
    if s.len() % 2 != 0 || !s.bytes().all(|c| c.is_ascii_digit() || (b'a'..=b'f').contains(&c)) {
        return None;
    }
    (0..s.len()).step_by(2).map(|i| u8::from_str_radix(&s[i..i + 2], 16).ok()).collect()
}

fn main() {
    let mut out = io::stdout().lock();
    for line in io::stdin().lock().lines() {
        let line = line.expect("stdin");
        let (op, arg) = line.split_once('\t').unwrap_or((&line, ""));
        let r = match op {
            "encode" => unhex(arg).map(|b| STANDARD.encode(b)),
            "decode" => STANDARD.decode(arg).ok().map(|b| hex(&b)),
            "encode_url" => unhex(arg).map(|b| URL_SAFE.encode(b)),
            "decode_url" => URL_SAFE.decode(arg).ok().map(|b| hex(&b)),
            _ => {
                writeln!(out, "unsupported").expect("stdout");
                continue;
            }
        };
        writeln!(out, "{}", r.map_or("err".into(), |v| format!("ok\t{v}"))).expect("stdout");
        out.flush().expect("stdout");
    }
}
