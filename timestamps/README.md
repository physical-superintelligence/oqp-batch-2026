# Checking the dated drafts

The folders under `<result>/drafts/2026-09-21/` contain earlier OQP27 and NPT
manuscripts, preserved byte for byte. FreeTSA and DigiCert signed the snapshot's digest on
**21 September 2026 at 19:17:23 UTC**.

With Python 3.9+ and OpenSSL 3, run from the repository root:

```sh
python3 -I timestamps/verify.py
```

To check just one result, append its directory name. A successful check prints
both signed times and the names of the verified files. It runs offline and
does not modify the drafts.

Each draft folder includes the original manifest, randomizer and Merkle path;
the shared signed receipts and public certificates are in [`2026-09-21/`](2026-09-21/).
The check follows each selected file through its manifest to the signed root,
then verifies both signatures, request nonces, certificate chains and archived
revocation lists at the signed time. The original manifests also list files
from the larger snapshot; only the selected files included here are checked.

The timestamps establish that these exact copies existed by the signed time.
The dated folders preserve earlier drafts; use the main papers for the current statements.

<details>
<summary>Independent checks</summary>

[`verify.py`](verify.py) uses SHA-256 and OpenSSL's RFC 3161 verifier. For each
original manifest `M` and 32-byte randomizer `N`, it reconstructs:

```text
C      = SHA256("PSI-RESULT-V1" || 0x00 || N || SHA256(M))
leaf   = SHA256(0x00 || C)
parent = SHA256(0x01 || left || right)
```

The resulting root must match `root.bin`, whose SHA-256 digest is signed by
both authorities. `timestamp/files.json` maps the filenames used here to the
paths in the original manifest. The new README files are navigation, outside
the timestamped material.

The verifier pins the SHA-256 fingerprints of the authorities' DER root
certificates. They can be checked against
[FreeTSA's root](https://freetsa.org/files/cacert.pem) and
[DigiCert Trusted Root G4](https://cacerts.digicert.com/DigiCertTrustedRootG4.crt).
Original certificate download URLs are retained in
[`SOURCES.json`](2026-09-21/certificates/SOURCES.json).

Protocol and command references: [RFC 3161](https://www.rfc-editor.org/rfc/rfc3161)
and [OpenSSL `ts`](https://docs.openssl.org/3.6/man1/openssl-ts/).

</details>
