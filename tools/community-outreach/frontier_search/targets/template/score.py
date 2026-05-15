#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--artifact", required=True)
    args = parser.parse_args()
    data = json.loads(Path(args.artifact).read_text(encoding="utf-8"))
    conflicts = int(data.get("conflicts", 999999))
    print(json.dumps({
        "ok": True,
        "score": conflicts,
        "summary": f"conflicts={conflicts}",
    }))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
