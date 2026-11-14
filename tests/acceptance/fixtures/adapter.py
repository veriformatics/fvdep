#!/usr/bin/env python3
"""Protocol-v1 adapter fixture; modes plant only the named defect."""
import json
import sys

ALPHABET = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"


def encode(raw):
    out = []
    for start in range(0, len(raw), 3):
        block = raw[start:start + 3]
        bits = int.from_bytes(block, "big") << (8 * (3 - len(block)))
        chars = [ALPHABET[(bits >> shift) & 63] for shift in (18, 12, 6, 0)]
        out.extend(chars[:len(block) + 1] + ["="] * (3 - len(block)))
    return "".join(out)


def decode(text, url=False):
    alphabet = ALPHABET.translate(str.maketrans("+/", "-_")) if url else ALPHABET
    if len(text) % 4:
        return None
    out = bytearray()
    for start in range(0, len(text), 4):
        block = text[start:start + 4]
        padding = len(block) - len(block.rstrip("="))
        if padding > 2 or (padding and start + 4 != len(text)):
            return None
        chars = block[:4 - padding]
        if any(char not in alphabet for char in chars):
            return None
        value = 0
        for char in chars:
            value = value * 64 + alphabet.index(char)
        unused = padding * 2
        if value & ((1 << unused) - 1):
            return None
        out.extend((value >> unused).to_bytes(3 - padding, "big"))
    return bytes(out)


def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else "match"
    for line in sys.stdin:
        if mode == "crash":
            return 17
        if mode == "missing":
            continue
        if mode == "not-json":
            print("not-json", flush=True)
            continue
        request = json.loads(line)
        if mode == "unsupported":
            reply = {"unsupported": True}
        elif mode == "invalid":
            reply = {"invalid": "planted invalid reply"}
        elif request.get("op") not in {"encode", "encodeUrl", "decode", "decodeUrl"}:
            reply = {"unsupported": True}
        elif mode == "some-unsupported" and request["args"] == [""]:
            reply = {"unsupported": True}
        elif mode == "mismatch":
            reply = {"ok": "this is not base64"}
        elif mode == "wrong-error":
            reply = {"err": "input rejected"}
        else:
            try:
                op = request["op"]
                if op in {"encode", "encodeUrl"}:
                    text = encode(bytes.fromhex(request["args"][0]))
                    reply = {"ok": text.translate(str.maketrans("+/", "-_")) if op == "encodeUrl" else text}
                else:
                    raw = decode(request["args"][0], url=op == "decodeUrl")
                    reply = {"err": "any rejection text is equivalent"} if raw is None else {"ok": raw.hex()}
            except (ValueError, TypeError, KeyError, IndexError):
                reply = {"invalid": "malformed request"}
        print(json.dumps(reply), flush=True)
        if mode == "extra":
            print(json.dumps(reply), flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
