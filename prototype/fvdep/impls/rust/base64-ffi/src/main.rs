//! fvdep adapter over the binding (ops encode, decode).
use std::io::{self, BufRead, Write};

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
            "encode" => unhex(arg).map(|b| fvdep_base64_ffi::encode(&b)),
            "decode" => fvdep_base64_ffi::decode(arg).map(|b| b.iter().map(|x| format!("{x:02x}")).collect()),
            _ => {
                writeln!(out, "unsupported").expect("stdout");
                continue;
            }
        };
        writeln!(out, "{}", r.map_or("err".into(), |v| format!("ok\t{v}"))).expect("stdout");
        out.flush().expect("stdout");
    }
}
