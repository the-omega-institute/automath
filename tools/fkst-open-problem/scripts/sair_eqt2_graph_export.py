#!/usr/bin/env python3
"""Export a SAIR-EQT2-only FKST graph and progress snapshot."""

from __future__ import annotations

import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
ARTIFACT_DIR = ROOT / "artifacts" / "sair-eqt2"
STATUS_PATH = Path("/tmp/fkst-sair-eqt2-status-for-graph.json")


NODES = {
    "tick": "omega_sair_stage2_tick",
    "seed": "seed_sair_stage2",
    "proposal": "omega_proposal",
    "proposal_intake": "proposal_intake",
    "consensus_proposal": "consensus.proposal",
    "consensus_decide": "consensus.decide",
    "consensus_converge": "consensus.consensus_converge",
    "converge_diagnostic": "converge_diagnostic",
    "artifact_task": "omega_artifact_task",
    "artifact_writer": "artifact_writer",
    "research_task": "omega_research_task",
    "research_portfolio": "research_portfolio",
    "candidate": "omega_candidate_search",
    "research_checker": "research_checker",
    "checker_result": "omega_checker_result",
    "research_artifact": "research_artifact",
    "codex_task": "omega_codex_research_task",
    "research_candidate": "research_candidate",
    "repo_artifact": "omega_repo_artifact",
    "repo_sink": "repo_artifact_sink",
    "claim_state": "claim_state.jsonl",
    "research_run": "research_run.jsonl",
}

EDGES = [
    ("tick", "seed", "cron 24h"),
    ("seed", "proposal", ""),
    ("proposal", "proposal_intake", ""),
    ("proposal_intake", "consensus_proposal", ""),
    ("consensus_proposal", "consensus_decide", "Codex consensus package"),
    ("consensus_decide", "consensus_converge", "diagnostic path"),
    ("consensus_converge", "converge_diagnostic", ""),
    ("converge_diagnostic", "artifact_task", ""),
    ("artifact_task", "artifact_writer", ""),
    ("artifact_writer", "repo_artifact", ""),
    ("seed", "research_task", ""),
    ("research_task", "research_portfolio", "default deterministic portfolio"),
    ("research_portfolio", "candidate", "3 candidates"),
    ("candidate", "research_checker", "local checker"),
    ("research_checker", "checker_result", ""),
    ("checker_result", "research_artifact", ""),
    ("research_artifact", "repo_artifact", ""),
    ("seed", "codex_task", ""),
    ("codex_task", "research_candidate", "opt-in FKST_SAIR_EQT2_CODEX=1"),
    ("research_candidate", "candidate", "Codex advisory candidate"),
    ("repo_artifact", "repo_sink", "FKST_GITHUB_WRITE=0"),
    ("repo_sink", "claim_state", "claim-state artifact"),
    ("repo_sink", "research_run", "research artifact"),
]


def load_jsonl(path: Path) -> list[dict]:
    if not path.exists():
        return []
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line]


def load_status() -> dict:
    if not STATUS_PATH.exists():
        return {}
    return json.loads(STATUS_PATH.read_text(encoding="utf-8"))


def render_mermaid(status: dict, research_rows: list[dict], claim_rows: list[dict]) -> str:
    lines = [
        "flowchart TD",
        "  classDef event fill:#eef6ff,stroke:#4d7fb8,color:#102033;",
        "  classDef dept fill:#f3f0ff,stroke:#7357c8,color:#20153f;",
        "  classDef artifact fill:#ecfff4,stroke:#3c8d5a,color:#10351f;",
        "  classDef disabled fill:#f5f5f5,stroke:#999,color:#555,stroke-dasharray: 4 4;",
    ]
    for node_id, label in NODES.items():
        safe_label = label.replace('"', "'")
        lines.append(f'  {node_id}["{safe_label}"]')
    for left, right, label in EDGES:
        edge = f"  {left} -->"
        if label:
            edge += f'|"{label}"|'
        edge += f" {right}"
        lines.append(edge)
    event_nodes = [
        "tick", "proposal", "consensus_proposal", "consensus_converge", "artifact_task",
        "research_task", "candidate", "checker_result", "codex_task", "repo_artifact",
    ]
    dept_nodes = [
        "seed", "proposal_intake", "consensus_decide", "converge_diagnostic",
        "artifact_writer", "research_portfolio", "research_checker",
        "research_artifact", "research_candidate", "repo_sink",
    ]
    artifact_nodes = ["claim_state", "research_run"]
    lines.append("  class " + ",".join(event_nodes) + " event;")
    lines.append("  class " + ",".join(dept_nodes) + " dept;")
    lines.append("  class " + ",".join(artifact_nodes) + " artifact;")
    lines.append("  class research_candidate,codex_task disabled;")
    health = status.get("health") or {}
    ledger = status.get("ledger") or {}
    lines.extend(
        [
            "",
            "%% Progress snapshot",
            f"%% status={status.get('status', 'unknown')}",
            f"%% graph={health.get('graph', 'unknown')}",
            f"%% pid={health.get('pid', 'unknown')} runtime_age_seconds={health.get('runtime_age_seconds', 'unknown')}",
            f"%% ledger_samples={ledger.get('samples', 'unknown')} ledger_errors={ledger.get('errors', 'unknown')}",
            f"%% research_rows={len(research_rows)} claim_rows={len(claim_rows)}",
        ]
    )
    return "\n".join(lines) + "\n"


def render_dot(status: dict) -> str:
    lines = [
        "digraph sair_eqt2_fkst {",
        "  rankdir=LR;",
        '  node [shape=box, style="rounded,filled", fillcolor="#eef6ff"];',
    ]
    for node_id, label in NODES.items():
        lines.append(f'  {node_id} [label="{label}"];')
    for left, right, label in EDGES:
        attr = f' [label="{label}"]' if label else ""
        lines.append(f"  {left} -> {right}{attr};")
    health = status.get("health") or {}
    lines.append(f'  progress [shape=note, fillcolor="#fff8dc", label="status={status.get("status", "unknown")}\\ngraph={health.get("graph", "unknown")}\\npid={health.get("pid", "unknown")}"];')
    lines.append("}")
    return "\n".join(lines) + "\n"


def render_markdown(status: dict, research_rows: list[dict], claim_rows: list[dict]) -> str:
    health = status.get("health") or {}
    ledger = status.get("ledger") or {}
    lines = [
        "# SAIR-EQT2 FKST Graph Progress",
        "",
        "## Status",
        "",
        f"- status: `{status.get('status', 'unknown')}`",
        f"- graph: `{health.get('graph', 'unknown')}`",
        f"- pid: `{health.get('pid', 'unknown')}`",
        f"- runtime_age_seconds: `{health.get('runtime_age_seconds', 'unknown')}`",
        f"- ledger_samples: `{ledger.get('samples', 'unknown')}`",
        f"- ledger_errors: `{ledger.get('errors', 'unknown')}`",
        f"- github_write: `{health.get('github_write', 'unknown')}`",
        "",
        "## Mermaid",
        "",
        "```mermaid",
        render_mermaid(status, research_rows, claim_rows).rstrip(),
        "```",
        "",
        "## Research Rows",
        "",
    ]
    for row in research_rows:
        lines.append(
            f"- `{row.get('candidate_action_id')}`: state=`{row.get('state')}`, checker_status=`{row.get('checker_status')}`"
        )
    lines.extend(["", "## Claim Rows", ""])
    for row in claim_rows:
        lines.append(f"- `{row.get('claim_id')}`: state=`{row.get('state')}`")
    lines.extend(
        [
            "",
            "## Boundaries",
            "",
            "- FKST consensus is routing state, not mathematical proof.",
            "- Mathematical truth must come from Lean/checker/source-replay/git artifacts.",
            "- GitHub write automation remains disabled.",
            "- Target is SAIR-EQT2 only.",
            "",
        ]
    )
    return "\n".join(lines)


def render_svg(status: dict, research_rows: list[dict], claim_rows: list[dict]) -> str:
    health = status.get("health") or {}
    rows = [
        [
            ("tick", "omega_sair_stage2_tick"),
            ("seed", "seed_sair_stage2"),
        ],
        [
            ("proposal", "omega_proposal"),
            ("proposal_intake", "proposal_intake"),
            ("consensus_proposal", "consensus.proposal"),
            ("consensus_decide", "consensus.decide"),
            ("consensus_converge", "consensus.converge"),
            ("converge_diagnostic", "converge_diagnostic"),
            ("artifact_writer", "artifact_writer"),
            ("claim_state", "claim_state.jsonl"),
        ],
        [
            ("research_task", "omega_research_task"),
            ("research_portfolio", "research_portfolio"),
            ("candidate", "omega_candidate_search"),
            ("research_checker", "research_checker"),
            ("checker_result", "omega_checker_result"),
            ("research_artifact", "research_artifact"),
            ("research_run", "research_run.jsonl"),
        ],
        [
            ("codex_task", "omega_codex_research_task"),
            ("research_candidate", "research_candidate opt-in"),
        ],
    ]
    positions: dict[str, tuple[int, int]] = {}
    x_gap = 180
    y_gap = 125
    box_w = 150
    box_h = 48
    margin = 40
    for row_index, row in enumerate(rows):
        y = margin + row_index * y_gap
        for col_index, (node_id, _) in enumerate(row):
            positions[node_id] = (margin + col_index * x_gap, y)

    edges = [
        ("tick", "seed", "cron"),
        ("seed", "proposal", ""),
        ("proposal", "proposal_intake", ""),
        ("proposal_intake", "consensus_proposal", ""),
        ("consensus_proposal", "consensus_decide", ""),
        ("consensus_decide", "consensus_converge", ""),
        ("consensus_converge", "converge_diagnostic", ""),
        ("converge_diagnostic", "artifact_writer", ""),
        ("artifact_writer", "claim_state", ""),
        ("seed", "research_task", ""),
        ("research_task", "research_portfolio", ""),
        ("research_portfolio", "candidate", "3 candidates"),
        ("candidate", "research_checker", ""),
        ("research_checker", "checker_result", ""),
        ("checker_result", "research_artifact", ""),
        ("research_artifact", "research_run", ""),
        ("seed", "codex_task", "disabled by default"),
        ("codex_task", "research_candidate", "FKST_SAIR_EQT2_CODEX=1"),
        ("research_candidate", "candidate", "advisory"),
    ]

    def esc(text: object) -> str:
        return (
            str(text)
            .replace("&", "&amp;")
            .replace("<", "&lt;")
            .replace(">", "&gt;")
            .replace('"', "&quot;")
        )

    width = 1360
    height = 610
    parts = [
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" viewBox="0 0 {width} {height}">',
        "<style>",
        "text{font-family:Arial,Helvetica,sans-serif;font-size:13px;fill:#172033}",
        ".title{font-size:20px;font-weight:700}",
        ".meta{font-size:12px;fill:#4d5566}",
        ".event{fill:#eef6ff;stroke:#4d7fb8;stroke-width:1.5}",
        ".dept{fill:#f3f0ff;stroke:#7357c8;stroke-width:1.5}",
        ".artifact{fill:#ecfff4;stroke:#3c8d5a;stroke-width:1.5}",
        ".disabled{fill:#f5f5f5;stroke:#999;stroke-width:1.5;stroke-dasharray:5 4}",
        ".edge{stroke:#7b8496;stroke-width:1.4;fill:none;marker-end:url(#arrow)}",
        ".edgeLabel{font-size:11px;fill:#5d6473}",
        "</style>",
        '<defs><marker id="arrow" markerWidth="10" markerHeight="10" refX="8" refY="3" orient="auto" markerUnits="strokeWidth"><path d="M0,0 L0,6 L9,3 z" fill="#7b8496"/></marker></defs>',
        '<rect x="0" y="0" width="1360" height="610" fill="#ffffff"/>',
        '<text class="title" x="40" y="28">SAIR-EQT2 FKST Portfolio Graph</text>',
        f'<text class="meta" x="40" y="50">status={esc(status.get("status", "unknown"))} graph={esc(health.get("graph", "unknown"))} pid={esc(health.get("pid", "unknown"))} runtime_age_seconds={esc(health.get("runtime_age_seconds", "unknown"))}</text>',
    ]

    for left, right, label in edges:
        x1, y1 = positions[left]
        x2, y2 = positions[right]
        start_x = x1 + box_w
        start_y = y1 + box_h / 2
        end_x = x2
        end_y = y2 + box_h / 2
        if end_x <= start_x:
            mid_y = (start_y + end_y) / 2
            path = f"M {start_x} {start_y} C {start_x + 35} {start_y}, {end_x - 35} {end_y}, {end_x} {end_y}"
        else:
            path = f"M {start_x} {start_y} L {end_x} {end_y}"
        parts.append(f'<path class="edge" d="{path}"/>')
        if label:
            parts.append(f'<text class="edgeLabel" x="{(start_x + end_x) / 2 - 30:.1f}" y="{(start_y + end_y) / 2 - 6:.1f}">{esc(label)}</text>')

    event_ids = {"tick", "proposal", "consensus_proposal", "consensus_converge", "research_task", "candidate", "checker_result", "codex_task"}
    artifact_ids = {"claim_state", "research_run"}
    disabled_ids = {"codex_task", "research_candidate"}
    for row in rows:
        for node_id, label in row:
            x, y = positions[node_id]
            cls = "artifact" if node_id in artifact_ids else "event" if node_id in event_ids else "dept"
            if node_id in disabled_ids:
                cls = "disabled"
            parts.append(f'<rect class="{cls}" x="{x}" y="{y}" width="{box_w}" height="{box_h}" rx="7"/>')
            parts.append(f'<text x="{x + 10}" y="{y + 28}">{esc(label)}</text>')

    parts.append('<text class="meta" x="40" y="555">Research rows: ' + esc(len(research_rows)) + " | Claim rows: " + esc(len(claim_rows)) + " | GitHub write disabled | FKST consensus is not proof</text>")
    parts.append("</svg>")
    return "\n".join(parts) + "\n"


def main() -> None:
    ARTIFACT_DIR.mkdir(parents=True, exist_ok=True)
    status = load_status()
    research_rows = load_jsonl(ARTIFACT_DIR / "research_run.jsonl")
    claim_rows = load_jsonl(ARTIFACT_DIR / "claim_state.jsonl")
    outputs = {
        "fkst_graph.mmd": render_mermaid(status, research_rows, claim_rows),
        "fkst_graph.dot": render_dot(status),
        "fkst_graph_progress.md": render_markdown(status, research_rows, claim_rows),
        "fkst_graph.svg": render_svg(status, research_rows, claim_rows),
    }
    for name, text in outputs.items():
        path = ARTIFACT_DIR / name
        path.write_text(text, encoding="utf-8")
        print(path)


if __name__ == "__main__":
    main()
