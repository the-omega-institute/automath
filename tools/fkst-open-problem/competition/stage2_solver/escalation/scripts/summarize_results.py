#!/usr/bin/env python3
"""Print and write a concise Markdown summary from results/*.json."""
import argparse
import json
import pathlib

ARTIFACT_ROOT = pathlib.Path(__file__).resolve().parents[1]


def build_parser():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--results-dir", type=pathlib.Path, default=ARTIFACT_ROOT / "results")
    parser.add_argument("--output", type=pathlib.Path, default=ARTIFACT_ROOT / "results" / "summary.md")
    return parser


def main():
    args = build_parser().parse_args()
    guided = json.load(open(args.results_dir / "guided_final.json"))
    blind = json.load(open(args.results_dir / "blind_spike.json"))
    sweep = json.load(open(args.results_dir / "guided_final_sweep.json"))

    sample = guided["sample_200"]
    hard2 = guided["hard2"]
    accepted_sweep = sum(1 for status in sweep.values() if status == "accepted")
    still_unsolved = guided["still_unsolved"]
    wrong_accepted = blind["accepted"] - blind["verdict_correct_of_accepted"]

    text = "\n".join([
        "# Result Summary",
        "",
        "| mode | scope | accepted | wrong accepted | status |",
        "|---|---|---:|---:|---|",
        f"| deterministic solo | sample_200 | {sample['solo_baseline']}/{sample['of']} | - | baseline |",
        f"| deterministic solo | hard2 | {hard2['solo_baseline']}/{hard2['of']} | - | baseline |",
        f"| guided escalation | {guided['of_unsolved']} residuals | {accepted_sweep}/{guided['of_unsolved']} | 0 | upper bound |",
        f"| blind spike | {blind['n']} residuals | {blind['accepted']}/{blind['n']} | {wrong_accepted} | preliminary |",
        "",
        f"Guided totals: sample_200 {sample['total']}/{sample['of']}; hard2 {hard2['total']}/{hard2['of']}.",
        f"Still unsolved after guided escalation: {', '.join(still_unsolved)}.",
        f"Blind not accepted: {', '.join(blind['not_accepted'])}.",
        "",
    ])
    args.output.write_text(text)
    print(text)


if __name__ == "__main__":
    main()
