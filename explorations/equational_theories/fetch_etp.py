"""Download the ETP data recorded in etp_version.json, and check it.

usage: fetch_etp.py DIR [--version FILE]

Every file listed in the version file is downloaded into DIR, at its
recorded path, unless DIR holds it already with the recorded checksum:
equations.txt and graph.json, which the explorations with the ETP graph as
background read, and the ETP's files of finite magmas, in DIR/magmas, which
they seed into the context. The magma files and equations.txt are pinned to
the recorded commit of the ETP's repository; graph.json comes from the ETP's
website, which may change it. A file whose checksum differs from the recorded
one is kept beside, as PATH.unverified, and the command fails.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
import urllib.request
from collections.abc import Sequence
from pathlib import Path

VERSION = Path(__file__).resolve().parent / "etp_version.json"


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def fetch(directory: Path, version: dict) -> list[str]:
    """Download the files of `version` into `directory`; return the paths of
    those whose checksum differs from the recorded one."""
    unverified = []
    for name, entry in version["files"].items():
        target = directory / entry["path"]
        if target.exists() and sha256(target.read_bytes()) == entry["sha256"]:
            continue
        with urllib.request.urlopen(entry["url"]) as response:
            data = response.read()
        target.parent.mkdir(parents=True, exist_ok=True)
        if sha256(data) != entry["sha256"]:
            target.with_name(target.name + ".unverified").write_bytes(data)
            unverified.append(entry["path"])
            continue
        target.write_bytes(data)
    return unverified


def main(argv: Sequence[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description="Download the ETP data recorded in etp_version.json, and check it.")
    parser.add_argument("directory", type=Path, metavar="DIR", help="where to put the files")
    parser.add_argument("--version", type=Path, default=VERSION, metavar="FILE",
                        help="the version file (default: etp_version.json next to this script)")
    args = parser.parse_args(argv)
    version = json.loads(args.version.read_text(encoding="utf-8"))
    unverified = fetch(args.directory, version)
    if unverified:
        sys.exit(f"Checksums differ from the recorded ones, files kept as .unverified: {', '.join(unverified)}")
    print(f"{len(version['files'])} files of ETP commit {version['commit'][:7]} in {args.directory}")


if __name__ == "__main__":
    main()
