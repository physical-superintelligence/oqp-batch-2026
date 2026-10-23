#!/usr/bin/env python3
"""Check that the definitions copied into Challenge.lean match the library verbatim.

Challenge.lean imports only Mathlib, so it repeats the definitions its statements use. Each
copy sits between a `-- verbatim: <path>` line and a `-- end verbatim` line, and must occur
character for character in the named library file. Comparator separately checks that the
copied constants and the library's constants are identical; this check keeps the two texts in
step so that a reader can audit either one.
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BLOCK = re.compile(r"^-- verbatim: (\S+)\n(.*?)\n-- end verbatim$", re.M | re.S)


def main() -> int:
    challenge = (ROOT / "Challenge.lean").read_text(encoding="utf-8")
    blocks = BLOCK.findall(challenge)
    failed = False
    if not blocks:
        print("Challenge.lean: no verbatim blocks found")
        return 1
    for path, body in blocks:
        source = ROOT / path
        if not source.is_file():
            print(f"Challenge.lean: verbatim source {path} does not exist")
            failed = True
        elif body not in source.read_text(encoding="utf-8"):
            first = body.strip().splitlines()[0]
            print(f"Challenge.lean: block starting {first!r} is not verbatim in {path}")
            failed = True
    print(f"{len(blocks)} verbatim blocks checked" + ("" if not failed else "; mismatches found"))
    return int(failed)


if __name__ == "__main__":
    raise SystemExit(main())
