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
    verified = bool(data.get("verified")) or int(data.get("conflicts", 1)) == 0
    print(json.dumps({
        "ok": True,
        "verified": verified,
        "summary": "verified" if verified else "not verified",
    }))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
