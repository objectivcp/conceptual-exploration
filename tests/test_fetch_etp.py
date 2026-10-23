"""Unit tests for downloading the ETP data recorded in etp_version.json."""

import hashlib
import io
import json

import pytest

from explorations.equational_theories import fetch_etp

FILES = {"https://etp/equations.txt": b"x = x\n", "https://etp/tables.txt": b"Table [[0]]\n"}


def version(**sha):
    entries = {
        "equations.txt": {"path": "equations.txt", "url": "https://etp/equations.txt"},
        "tables.txt": {"path": "magmas/tables.txt", "url": "https://etp/tables.txt"},
    }
    for name, entry in entries.items():
        entry["sha256"] = sha.get(name.split(".")[0], hashlib.sha256(FILES[entry["url"]]).hexdigest())
    return {"commit": "1aec8a7acf22", "files": entries}


@pytest.fixture
def downloads(monkeypatch):
    urls = []

    def urlopen(url):
        urls.append(url)
        return io.BytesIO(FILES[url])
    monkeypatch.setattr(fetch_etp.urllib.request, "urlopen", urlopen)
    return urls


def test_the_files_are_downloaded_to_their_paths_and_kept_when_valid(tmp_path, downloads):
    assert fetch_etp.fetch(tmp_path, version()) == []
    assert (tmp_path / "magmas" / "tables.txt").read_bytes() == FILES["https://etp/tables.txt"]
    # Already there with the recorded checksum: not downloaded again.
    assert fetch_etp.fetch(tmp_path, version()) == []
    assert len(downloads) == 2


def test_a_file_with_another_checksum_is_kept_aside_and_reported(tmp_path, downloads):
    assert fetch_etp.fetch(tmp_path, version(tables="0" * 64)) == ["magmas/tables.txt"]
    assert not (tmp_path / "magmas" / "tables.txt").exists()
    assert (tmp_path / "magmas" / "tables.txt.unverified").exists()


def test_the_command_fails_on_a_differing_checksum(tmp_path, downloads):
    path = tmp_path / "version.json"
    path.write_text(json.dumps(version(equations="0" * 64)))
    with pytest.raises(SystemExit, match="equations.txt"):
        fetch_etp.main([str(tmp_path / "data"), "--version", str(path)])
