#!/usr/bin/env python3
"""L7 byte-comparison property: unequal bytes fail --check and stay unequal."""

from pathlib import Path
import random
import sys


def main() -> None:
    path = Path(sys.argv[1]).resolve(strict=True)
    seed = int(sys.argv[2])
    sample = int(sys.argv[3])
    data = path.read_bytes()
    rng = random.Random(seed ^ (sample * 0x9E3779B9))
    if sample % 4 == 3 or not data:
        changed = data + bytes([rng.randrange(256)])
        offset = len(data)
    elif sample % 4 == 2:
        offset = rng.randrange(len(data))
        changed = data[:offset] + data[offset + 1 :]
    else:
        offset = rng.randrange(len(data))
        delta = rng.randrange(1, 256)
        changed = data[:offset] + bytes([data[offset] ^ delta]) + data[offset + 1 :]
    if changed == data:
        raise AssertionError("The mutation must change the document bytes.")
    path.write_bytes(changed)
    line = data[:offset].count(b"\n") + 1
    print(f"MUTATE seed={seed} sample={sample} offset={offset} line={line} bytes={len(data)}->{len(changed)}")


if __name__ == "__main__":
    main()
