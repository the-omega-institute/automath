import csv
import json
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
CERT = ROOT / "certificates" / "cicm_search_transcript.json"
SCRIPT = ROOT / "certificates" / "emit_cicm_screen_csv.py"
EXPECTED_HEADER = [
    "year",
    "venue",
    "title",
    "doi_or_arxiv",
    "included_excluded",
    "keyword_hit",
    "rationale",
]


def test_cicm_screen_transcript_emits_reviewer_csv_schema():
    output = subprocess.check_output(
        [sys.executable, str(SCRIPT), str(CERT)], cwd=ROOT, text=True
    )
    rows = list(csv.DictReader(output.splitlines()))
    assert rows
    assert csv.DictReader(output.splitlines()).fieldnames == EXPECTED_HEADER
    assert len(rows) >= 20
    assert {row["included_excluded"] for row in rows} == {"included", "excluded"}
    assert all(row["year"] and row["venue"] and row["title"] for row in rows)
    assert all(row["doi_or_arxiv"] for row in rows)
    assert all(row["keyword_hit"] for row in rows)
    assert all(row["rationale"] for row in rows)


def test_cicm_screen_json_contains_row_level_screened_papers():
    data = json.loads(CERT.read_text(encoding="utf-8"))
    screened = data["screened_papers"]
    assert len(screened) >= 20
    titles = [row["title"] for row in screened]
    assert len(titles) == len(set(titles))
    assert "included_hits" in data
    assert "excluded_hits" in data
    assert not any("category" in row for row in screened)
    for row in screened:
        assert set(EXPECTED_HEADER).issubset(row)
