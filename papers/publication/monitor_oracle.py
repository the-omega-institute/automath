#!/usr/bin/env python3
"""Monitor oracle queue: report new reviews and their verdicts."""

import json
import re
import sys
import time
import urllib.request
from pathlib import Path

SERVER = "http://localhost:8765"
DONE_DIR = Path(__file__).parent / "oracle" / "done"
STATE_FILE = Path(__file__).parent / "oracle" / ".monitor_state.json"


def get_status():
    try:
        resp = urllib.request.urlopen(f"{SERVER}/status", timeout=5)
        return json.loads(resp.read().decode("utf-8"))
    except Exception:
        return None


def get_all_reviews():
    """Get all gate review files with sizes."""
    reviews = {}
    for f in DONE_DIR.glob("*_gate_R*.md"):
        reviews[f.name] = {
            "size": f.stat().st_size,
            "mtime": f.stat().st_mtime,
            "path": str(f),
        }
    return reviews


def extract_verdict(filepath):
    """Extract verdict from a review file."""
    try:
        text = Path(filepath).read_text(encoding="utf-8", errors="replace")
        # Skip metadata
        if text.startswith("<!--"):
            text = text.split("-->", 1)[-1].strip()

        verdict = "UNKNOWN"

        # Strategy 1: Look for "Overall assessment" line with verdict on same or next line
        lines = text.split("\n")
        for i, line in enumerate(lines):
            low = line.lower().strip()
            # Check if this line has the assessment label
            if "overall assessment" in low or "my recommendation is" in low:
                # Check this line and next 2 lines for verdict keywords
                check_text = " ".join(
                    lines[j].lower() for j in range(i, min(i + 3, len(lines)))
                )
                if "reject" in check_text:
                    verdict = "REJECT"
                elif "major" in check_text:
                    verdict = "MAJOR_REV"
                elif "minor" in check_text:
                    verdict = "MINOR_REV"
                elif "accept" in check_text:
                    verdict = "ACCEPT"
                break

        # Strategy 2: Fallback — scan first 800 chars for verdict words
        # but exclude negations like "not accept", "needed to reach acceptance"
        if verdict == "UNKNOWN":
            head = text[:800].lower()
            # Remove common false-positive phrases
            cleaned = head.replace("not accept", "").replace("needed to reach accept", "")
            cleaned = cleaned.replace("would not recommend accept", "")
            cleaned = cleaned.replace("improvements needed", "")
            if "reject" in cleaned:
                verdict = "REJECT"
            elif "major revision" in cleaned or "major rev" in cleaned:
                verdict = "MAJOR_REV"
            elif "minor revision" in cleaned or "minor rev" in cleaned:
                verdict = "MINOR_REV"
            elif "accept" in cleaned:
                verdict = "ACCEPT"

        return verdict
    except Exception:
        return "ERROR"


def load_state():
    if STATE_FILE.exists():
        return json.loads(STATE_FILE.read_text())
    return {"known_reviews": {}, "last_completed": 0}


def save_state(state):
    STATE_FILE.write_text(json.dumps(state, indent=2))


def main():
    state = load_state()
    status = get_status()
    reviews = get_all_reviews()

    # Find new reviews
    new_reviews = []
    for name, info in reviews.items():
        if name not in state["known_reviews"]:
            new_reviews.append((name, info))
        elif info["mtime"] > state["known_reviews"].get(name, {}).get("mtime", 0):
            new_reviews.append((name, info))

    new_reviews.sort(key=lambda x: x[1]["mtime"])

    # Report
    ts = time.strftime("%H:%M:%S")
    if status:
        q = status["queue_length"]
        c = status["completed"]
        p = status.get("pending", "?")
        delta = c - state.get("last_completed", 0)
        print(f"[{ts}] Queue: {q} pending | Completed: {c} (+{delta}) | Current: {p}")
        state["last_completed"] = c
    else:
        print(f"[{ts}] Oracle server not responding")

    if new_reviews:
        print(f"[{ts}] === {len(new_reviews)} NEW REVIEW(S) ===")
        for name, info in new_reviews:
            size = info["size"]
            is_real = size > 5000
            is_stub = size < 1500
            verdict = extract_verdict(info["path"]) if is_real else "STUB"
            marker = ""
            if verdict == "ACCEPT":
                marker = " *** ACCEPT ***"
            elif verdict == "MINOR_REV":
                marker = " ** CLOSE **"
            elif verdict == "REJECT":
                marker = " ! REJECT"
            print(f"  {name:45s} {size:6d}B  {verdict}{marker}")
    else:
        print(f"[{ts}] No new reviews since last check.")

    # Tally all verdicts for real reviews
    verdicts = {"ACCEPT": [], "MINOR_REV": [], "MAJOR_REV": [], "REJECT": [], "STUB": [], "UNKNOWN": []}
    for name, info in sorted(reviews.items()):
        if info["size"] > 5000:
            v = extract_verdict(info["path"])
        elif info["size"] < 1500:
            v = "STUB"
        else:
            v = "UNKNOWN"
        verdicts[v].append(name)

    # Print summary only when explicitly requested or new reviews arrived
    if new_reviews or "--summary" in sys.argv:
        print(f"\n[{ts}] === VERDICT SUMMARY (latest real reviews per paper) ===")
        # Group by paper, keep only latest round
        paper_latest = {}
        for name in reviews:
            m = re.match(r"(.+)_gate_R(\d+)", name)
            if m:
                paper, rnd = m.group(1), int(m.group(2))
                if paper not in paper_latest or rnd > paper_latest[paper][0]:
                    paper_latest[paper] = (rnd, name, reviews[name])

        counts = {"ACCEPT": 0, "MINOR_REV": 0, "MAJOR_REV": 0, "REJECT": 0, "STUB": 0}
        for paper in sorted(paper_latest):
            rnd, name, info = paper_latest[paper]
            if info["size"] > 5000:
                v = extract_verdict(info["path"])
            else:
                v = "STUB"
            counts[v] = counts.get(v, 0) + 1
            icon = {"ACCEPT": "+", "MINOR_REV": "~", "MAJOR_REV": "-", "REJECT": "X", "STUB": "?"}
            print(f"  [{icon.get(v,'?')}] {paper:35s} R{rnd:2d}  {v}")

        print(f"\n  ACCEPT={counts['ACCEPT']} MINOR={counts['MINOR_REV']} "
              f"MAJOR={counts['MAJOR_REV']} REJECT={counts['REJECT']} STUB={counts['STUB']}")

    # Update state
    for name, info in reviews.items():
        state["known_reviews"][name] = {"mtime": info["mtime"], "size": info["size"]}
    save_state(state)


if __name__ == "__main__":
    main()
