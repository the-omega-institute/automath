#!/usr/bin/env python3
"""Export replay manifests from accepted certificate JSONL files."""
import argparse
import json
import pathlib
import re

ARTIFACT_ROOT = pathlib.Path(__file__).resolve().parents[1]
JUDGE_COMMIT = "6805e2323018fbd8a85f41ca09fc33d74d5a02a5"
JUDGE_POLICY = "DEFAULT_PROOF_POLICY"


def build_parser():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cert-dir", type=pathlib.Path, default=ARTIFACT_ROOT / "certs")
    parser.add_argument("--manifest-dir", type=pathlib.Path, default=ARTIFACT_ROOT / "manifests")
    return parser


def certificate_kind(row):
    code = row.get("code", "")
    if "finOpTable" in code or "decideFin" in code:
        out = {"certificate_kind": "finite_magma_countermodel"}
        match = re.search(r"\bFin\s+(\d+)\b", code)
        if match:
            out["magma_size"] = int(match.group(1))
        return out
    return {"certificate_kind": "lean_proof"}


def rows_for(path, mode):
    with path.open() as fh:
        for index, line in enumerate(fh):
            if not line.strip():
                continue
            cert = json.loads(line)
            row = {
                "id": cert["id"],
                "set": cert["set"],
                "mode": mode,
                "truth": cert["truth"],
                "chosen_verdict": cert["verdict"],
                "certificate_file": str(path.relative_to(ARTIFACT_ROOT)),
                "certificate_index": index,
                "judge_status": "accepted",
                "judge_policy": JUDGE_POLICY,
                "judge_commit": JUDGE_COMMIT,
            }
            row.update(certificate_kind(cert))
            yield row


def write_jsonl(path, rows):
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w") as fh:
        for row in rows:
            fh.write(json.dumps(row, sort_keys=True) + "\n")


def main():
    args = build_parser().parse_args()
    guided = list(rows_for(args.cert_dir / "guided_certs.jsonl", "guided"))
    blind = list(rows_for(args.cert_dir / "blind_spike_certs.jsonl", "blind_spike"))
    write_jsonl(args.manifest_dir / "certificate_replay_manifest.jsonl", guided + blind)
    write_jsonl(args.manifest_dir / "guided_manifest.jsonl", guided)


if __name__ == "__main__":
    main()
