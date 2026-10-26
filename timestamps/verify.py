#!/usr/bin/env python3
"""Check the selected September drafts against their original timestamp receipts.

Requires Python 3.9+ and OpenSSL 3. Reads local files only.
"""

import argparse
import datetime as dt
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parents[1]
DATE = "2026-09-21"
DOMAIN = b"PSI-RESULT-V1\x00"
AUTHORITIES = {
    "freetsa": {
        "root": "a6379e7cecc05faa3cbf076013d745e327bbbaa38c0b9af22469d4701d18aabc",
        "chain": "freetsa-signer.pem",
        "crls": ["freetsa-32e841a95cc11641.crl"],
    },
    "digicert": {
        "root": "552f7bdcf1a7af9e6ce672017f4f12abf77240c78e761ac203d1d9d20ac89988",
        "chain": "digicert-chain.pem",
        "crls": ["digicert-2da09da7f4131f9f.crl", "digicert-ca0b1554ecd901ea.crl"],
    },
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha256(data):
    return hashlib.sha256(data).digest()


def file_at(base, relative):
    p = PurePosixPath(relative)
    require(p.parts and not p.is_absolute() and p.as_posix() == relative
            and ".." not in p.parts and "\\" not in relative,
            f"Unsafe path: {relative}")
    target = base
    for part in p.parts:
        target = target / part
        require(not target.is_symlink(), f"Linked path: {target}")
    require(target.is_file(), f"Missing file: {target}")
    return target


def load(path):
    return json.loads(path.read_text(encoding="utf-8"))


def openssl(*args):
    proc = subprocess.run(
        ["openssl", *map(str, args)], capture_output=True, timeout=30,
        env={**os.environ, "LC_ALL": "C"},
    )
    require(proc.returncode == 0,
            proc.stderr.decode(errors="replace").strip() or "OpenSSL failed")
    return proc.stdout


def check_receipts(shared):
    root_path = file_at(shared, "root.bin")
    root = root_path.read_bytes()
    require(len(root) == 32, "The batch root must be 32 bytes")
    require(openssl("version").startswith(b"OpenSSL 3."), "OpenSSL 3 is required")
    config = load(file_at(shared, "authorities.json"))
    require(len(config) == 2 and {a["name"] for a in config} == set(AUTHORITIES),
            "Both original timestamp authorities are required")
    times = []
    with tempfile.TemporaryDirectory(prefix="oqp-timestamps-") as temp:
        for authority in config:
            name = authority["name"]
            spec = AUTHORITIES[name]
            ca = file_at(shared, f"certificates/{name}-root.pem")
            chain = file_at(shared, "certificates/" + spec["chain"])
            require(sha256(openssl("x509", "-in", ca, "-outform", "DER")).hex()
                    == spec["root"], f"Unexpected trust root: {name}")
            for path, key in [(ca, "root_certificate_sha256"),
                              (chain, "chain_certificate_sha256")]:
                require(sha256(path.read_bytes()).hex() == authority[key],
                        f"Changed certificate: {path.name}")
            response = file_at(shared, name + ".tsr")
            request = file_at(shared, name + ".tsq")
            for path, key in [(response, "response_sha256"), (request, "request_sha256")]:
                require(sha256(path.read_bytes()).hex() == authority[key],
                        f"Changed original receipt or request: {path.name}")
            query = openssl("ts", "-query", "-in", request, "-text").decode()
            require(re.search(r"^Nonce:\s*0x[0-9a-fA-F]+\s*$", query, re.MULTILINE),
                    f"Missing request nonce: {name}")
            text = openssl("ts", "-reply", "-in", response, "-text").decode()
            match = re.search(r"^Time stamp:\s*(.+)$", text, re.MULTILINE)
            require(match is not None, f"Missing signed time: {name}")
            signed = dt.datetime.strptime(match.group(1).strip(), "%b %d %H:%M:%S %Y GMT")
            signed = signed.replace(tzinfo=dt.timezone.utc)
            require(signed.date().isoformat() == DATE, f"Unexpected date: {name}")
            # The archived, signed CRLs are checked at the timestamp's generation time.
            trust = openssl("x509", "-in", ca, "-outform", "PEM")
            for filename in spec["crls"]:
                crl = file_at(shared, "certificates/revocation/" + filename)
                fmt = "PEM" if crl.read_bytes().startswith(b"-----BEGIN") else "DER"
                trust += b"\n" + openssl("crl", "-inform", fmt, "-in", crl, "-outform", "PEM")
            trust_path = Path(temp) / (name + ".pem")
            trust_path.write_bytes(trust)
            args = ["ts", "-verify", "-in", response, "-CAfile", trust_path,
                    "-untrusted", chain, "-attime", str(int(signed.timestamp())),
                    "-crl_check_all"]
            for option, path in [("-data", root_path), ("-queryfile", request)]:
                require(b"Verification: OK" in openssl(*args, option, path),
                        f"Timestamp verification failed: {name}")
            times.append((name, signed.isoformat().replace("+00:00", "Z")))
    return root, times


def check_draft(folder, root):
    bundles = load(file_at(folder, "timestamp/files.json"))
    require(isinstance(bundles, list) and bundles, "No selected bundles")
    selected, ids = set(), set()
    for bundle in bundles:
        rid = bundle["id"]
        require(re.fullmatch(r"[a-z0-9_]+", rid) and rid not in ids, "Invalid or repeated result ID")
        ids.add(rid)
        prefix = "timestamp/" + rid + "/"
        manifest_path = file_at(folder, prefix + "MANIFEST.json")
        manifest = load(manifest_path)
        require(manifest["schema"] == "psi-private-result-manifest-v1"
                and manifest["result_id"] == rid, "Wrong original manifest")
        entries = {entry["path"]: entry for entry in manifest["files"]}
        require(len(entries) == len(manifest["files"]), "Repeated manifest path")
        files = bundle["files"]
        require(isinstance(files, dict) and files, "No selected files")
        for local, original in files.items():
            require(local not in selected and local != "README.md"
                    and not local.startswith("timestamp/"), "Invalid or repeated selection")
            selected.add(local)
            data = file_at(folder, local).read_bytes()
            require(original in entries, f"Not in the original manifest: {original}")
            entry = entries[original]
            require(len(data) == entry["bytes"] and sha256(data).hex() == entry["sha256"],
                    f"File does not match the dated copy: {folder.name}/{local}")
        nonce = file_at(folder, prefix + "nonce.bin").read_bytes()
        require(len(nonce) == 32, "Invalid commitment randomizer")
        commitment = sha256(DOMAIN + nonce + sha256(manifest_path.read_bytes()))
        require(commitment == file_at(folder, prefix + "commitment.bin").read_bytes(),
                "Original manifest commitment does not match")
        inclusion = load(file_at(folder, prefix + "inclusion.json"))
        require(inclusion["schema"] == "psi-merkle-inclusion-v1", "Wrong inclusion format")
        pos, width = inclusion["leaf_index"], inclusion["leaf_count"]
        require(0 <= pos < width, "Invalid Merkle position")
        h = sha256(b"\x00" + commitment)
        for step in inclusion["siblings"]:
            sibling = bytes.fromhex(step["sha256"])
            side = "left" if pos % 2 else "right"
            require(width > 1 and len(sibling) == 32 and step["side"] == side,
                    "Invalid Merkle path")
            if pos == width - 1 and width % 2:
                require(sibling == h, "Invalid duplicated Merkle node")
            h = sha256(b"\x01" + (sibling + h if side == "left" else h + sibling))
            pos, width = pos // 2, (width + 1) // 2
        require(width == 1 and h == root and inclusion["root"] == root.hex(),
                "Draft does not lead to the signed batch root")
    actual = {p.relative_to(folder).as_posix() for p in folder.rglob("*")
              if p.is_file() and p.relative_to(folder).parts[0] != "timestamp"
              and p.relative_to(folder).as_posix() != "README.md"}
    require(actual == selected, "Unlisted manuscript files in draft folder")
    return sorted(selected)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("result", nargs="?", help="Result directory, or omit to check all dated drafts")
    args = parser.parse_args()
    if args.result:
        require(re.fullmatch(r"[a-z0-9-]+", args.result), "Use a result directory name")
        folders = [ROOT / args.result / "drafts" / DATE]
    else:
        folders = sorted(ROOT.glob("*/drafts/" + DATE))
    require(folders, "No dated drafts found")
    root, times = check_receipts(ROOT / "timestamps" / DATE)
    checked = [(p, check_draft(p, root)) for p in folders]
    for name, time in times:
        print(f"{name}: signature, request, data and archived revocation checks OK; {time}")
    for folder, files in checked:
        suffix = "" if len(files) == 1 else "s"
        print(f"{folder.parents[1].name}: {len(files)} archived file{suffix} OK ({', '.join(files)})")
    suffix = "" if len(checked) == 1 else "s"
    print(f"Verified {sum(len(files) for _, files in checked)} selected files in {len(checked)} draft folder{suffix}.")


if __name__ == "__main__":
    try:
        main()
    except (ValueError, KeyError, TypeError, OSError, subprocess.TimeoutExpired) as error:
        print(f"Verification failed: {error}", file=sys.stderr)
        sys.exit(1)
