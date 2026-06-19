#!/usr/bin/env python3
"""Reference checker for the printed Stage-A Horn closure calculation.

The checker is deliberately small.  It contains the finite Horn rules printed
in the paper and computes only the projection of the least forward-chaining
closure onto the six public coordinates.  It does not parse TeX, prove ScanOK,
or assert script conformance.
"""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass
from typing import Iterable


COORDINATES = ("qinv", "qrgs", "qsrc", "qart", "qext", "qven")


class BranchBaseError(ValueError):
    """Raised when an input base violates the paper's closed-coordinate frame."""


@dataclass(frozen=True)
class Rule:
    rule_id: str
    premises: tuple[str, ...]
    conclusion: str


@dataclass(frozen=True)
class PrintedSystem:
    rules: tuple[Rule, ...]
    coordinates: tuple[str, ...]
    branches: dict[str, frozenset[str]]


def load_printed_system() -> PrintedSystem:
    a_rec = frozenset(
        {
            "pubAbs",
            "suppMain",
            "invJson",
            "invMd",
            "finalDigest",
            "mainTex",
            "stageAHornSchema",
            "stageAManifest",
            "stageAHornCertificate",
            "stageAReplayReport",
            "RecordGateOK",
            "CertDAGOK",
            "DigestOKstage_a",
            "srcInterface",
            "caseArtifacts",
            "venueReadiness",
            "qrgsReplayUpgrade",
        }
    )
    a_scan = a_rec | {"scanOK"}
    a_plus = a_scan | {"ScriptOKstage_a"}
    rules = (
        Rule("R0", ("pubAbs", "suppMain"), "singleRouteSurface"),
        Rule("R1", ("mainTex", "invJson", "invMd", "finalDigest", "scanOK"), "qinv"),
        Rule("R2", ("qinv",), "localInventoryClosed"),
        Rule(
            "R3",
            (
                "stageAHornSchema",
                "stageAManifest",
                "stageAHornCertificate",
                "stageAReplayReport",
                "finalDigest",
                "RecordGateOK",
                "CertDAGOK",
                "DigestOKstage_a",
                "ScriptOKstage_a",
                "qrgsReplayUpgrade",
            ),
            "qrgs",
        ),
        Rule("R4", ("qrgs",), "boundedReplayRecordGateSoundness"),
        Rule("R5", ("freshFormalSourceUpgrade",), "qsrc"),
        Rule("R6", ("dynamicArtifactSemanticUpgrade",), "qart"),
        Rule("R7a", ("stableLocator", "archiveByteEquality"), "locatorOKstageA"),
        Rule("R7b", ("locatorOKstageA", "externalArchiveEquivalence"), "qext"),
        Rule("R8", ("uploadTimeVenueAcceptanceUpgrade",), "qven"),
        Rule("R9", ("srcInterface",), "boundedSourceInterface"),
        Rule("R10", ("caseArtifacts",), "boundedArtifactRows"),
        Rule("R11", ("venueReadiness",), "datedVenueReadiness"),
        Rule(
            "R12",
            (
                "pubAbs",
                "suppMain",
                "stageAHornSchema",
                "stageAHornCertificate",
                "stageAReplayReport",
                "invJson",
                "invMd",
                "finalDigest",
            ),
            "routeSurfaceQuotient",
        ),
    )
    return PrintedSystem(
        rules=rules,
        coordinates=COORDINATES,
        branches={"A_rec": a_rec, "A_scan": a_scan, "A_plus": a_plus},
    )


def forward_closure(rules: Iterable[Rule], atoms: Iterable[str]) -> frozenset[str]:
    closure = set(atoms)
    changed = True
    while changed:
        changed = False
        for rule in rules:
            if rule.conclusion not in closure and all(
                premise in closure for premise in rule.premises
            ):
                closure.add(rule.conclusion)
                changed = True
    return frozenset(closure)


def closure_projection(system: PrintedSystem, branch_or_atoms: str | Iterable[str]) -> list[str]:
    if isinstance(branch_or_atoms, str):
        try:
            atoms = system.branches[branch_or_atoms]
        except KeyError as exc:
            raise BranchBaseError(f"unknown branch: {branch_or_atoms}") from exc
    else:
        atoms = frozenset(branch_or_atoms)

    coordinate_inputs = set(atoms).intersection(system.coordinates)
    if coordinate_inputs:
        raise BranchBaseError(
            "input bases must not contain public coordinates: "
            + ", ".join(sorted(coordinate_inputs))
        )

    closure = forward_closure(system.rules, atoms)
    return [coordinate for coordinate in system.coordinates if coordinate in closure]


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "branch",
        nargs="?",
        choices=("A_rec", "A_scan", "A_plus", "all"),
        default="all",
    )
    args = parser.parse_args(argv)

    system = load_printed_system()
    names = system.branches.keys() if args.branch == "all" else (args.branch,)
    result = {
        name: closure_projection(system, name)
        for name in names
    }
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    sys.exit(main())
