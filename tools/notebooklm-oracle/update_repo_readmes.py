#!/usr/bin/env python3
"""Update standalone paper repo READMEs with innovation summaries and video links.

Usage: python update_repo_readmes.py [--dry-run]
"""

import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ORG = "the-omega-institute"

PAPERS = [
    {
        "repo": "branch-cubic-regular-s4-closure-prym-ray-class",
        "title": "A Quartic Cover of 37a1 and Its Regular S4-Closure",
        "innovation": "For the conductor-37 elliptic curve, we carry out a complete explicit programme: constructing the regular S4-closure of a degree-4 map, decomposing the Jacobian via rational idempotents into a genus-2 Jacobian, a resolvent elliptic curve, and a Prym threefold. The branch cubic's splitting field is identified as a cubic ray class field that simultaneously sources a weight-1 cusp form and the 2-torsion field of the genus-2 Jacobian. Wild conductor contributions at p=3 are isolated exactly using p-adic cluster pictures.",
        "scope": "Arithmetic geometry",
        "keywords": ["elliptic curves", "Galois covers", "Jacobian decomposition", "Prym varieties", "ray class fields"],
        "journal": "Journal of Number Theory",
        "theorems": 39,
    },
    {
        "repo": "fibonacci-moduli-cross-resolution-arithmetic",
        "title": "Upper Fibers and Witness Covers for the Fibonacci Order-of-Apparition Map",
        "innovation": "We introduce witness covers for the fiber B_n (divisors of F_n whose rank of apparition equals n), proving B_n is an upper set in the divisor lattice obtained by removing covering ideals at maximal proper divisors. Minimal generators of B_n are classified via a primitive-vs-ladder dichotomy for atomic prime-power birth moduli. Both B_n and its minimal-generator set admit unique factorizations into connected coordinate blocks, yielding partition-lattice formulas and Bell-type lower bounds.",
        "scope": "Combinatorial number theory",
        "keywords": ["Fibonacci sequences", "rank of apparition", "divisor lattices", "multiplicative number theory"],
        "journal": "Research in Number Theory",
        "theorems": 29,
    },
    {
        "repo": "fibonacci-stabilization-sharp-threshold-conjugacy-nonlinearity",
        "title": "A Sharp Three-Window Threshold and Finite-Memory Conjugacy in Fibonacci Stabilization",
        "innovation": "A sharp threshold is proved at window size m=3: for all m>=3 the stabilized-window map is injective with image topologically conjugate to the full two-shift, while at m=2 injectivity fails on a single branch orbit with exact entropy and KL-defect formulas. The conjugacy transports the full thermodynamic formalism (invariant measures, entropy, pressure, equilibrium states) exactly, and fibers are characterized by explicit residue and discrete Fourier formulas.",
        "scope": "Symbolic dynamics and ergodic theory",
        "keywords": ["subshifts of finite type", "topological conjugacy", "thermodynamic formalism", "Fibonacci numeration"],
        "journal": "Journal of Physics A",
        "theorems": 70,
    },
    {
        "repo": "folded-rotation-histogram-certificates",
        "title": "Folded Histograms of Irrational Rotations: Sampling Certificates and Structural Mismatch to the Parry Measure",
        "innovation": "A two-stage audit framework for coarse-grained orbit data: stage one certifies whether an empirical folded histogram is close to its deterministic limit (via star-discrepancy, TV, and relative-entropy bounds), stage two tests compatibility with the ambient Parry equilibrium. The Fibonacci weighting is proved uniquely characterized by a contiguous numeration axiom, and the optimal injective placement barrier for lossless coarse-grainings is calibrated exactly.",
        "scope": "Applied dynamical systems",
        "keywords": ["irrational rotations", "Sturmian sequences", "Parry measure", "Renyi divergence", "statistical auditing"],
        "journal": "SIAM Journal on Applied Dynamical Systems",
        "theorems": 46,
    },
    {
        "repo": "folded-rotation-histogram",
        "title": "Zeckendorf Folds, Sturmian Rigidity, and Parry Divergence on the Golden-Mean Shift",
        "innovation": "The canonical Zeckendorf fold Fold_m on the Sturmian slice is bijective and realizes the higher-block presentation, giving an exact KL formula and sharp support-constrained Renyi minima in closed form. For m>=6 the exact optimal injective placement into the golden-mean language is determined, and the universal injective-placement barrier for lossless coarse-grainings into primitive SFTs is established.",
        "scope": "Ergodic theory and symbolic dynamics",
        "keywords": ["Sturmian subshifts", "Zeckendorf numeration", "golden-mean shift", "Parry measure", "Renyi divergence"],
        "journal": "Ergodic Theory and Dynamical Systems",
        "theorems": 46,
    },
    {
        "repo": "grg-shell-geometry-from-stationary-detector-thermality",
        "title": "Shell Geometry from Stationary Detector Thermality in Static KMS Spacetimes",
        "innovation": "Full click-record statistics of an Unruh-DeWitt detector define two codimension-one shells in static KMS spacetimes: an exact-clock shell (calibrated Tolman isotherm where detector output lies on the golden-mean shift) and a finite-recovery memory-transition shell. In Schwarzschild the shell pair determines the mass parameter via a self-calibrating two-mode ratio law that exactly cancels common response amplitude, yielding a local inverse principle for static spherical metrics.",
        "scope": "Mathematical physics / QFT in curved spacetime",
        "keywords": ["Unruh-DeWitt detectors", "KMS states", "black hole thermodynamics", "symbolic dynamics", "Hawking radiation"],
        "journal": "General Relativity and Gravitation",
        "theorems": 122,
    },
    {
        "repo": "resolution-folding-core-symbolic-dynamics",
        "title": "Finite-Window Rigidity in Fibonacci Numeration",
        "innovation": "The Zeckendorf fold map is the normal-form map of a finite terminating confluent rewrite system, with a sharp block-bijection threshold at m=3. For m>=3 the block map is a bijection with exact local inverse rules, the right Fischer cover is identified as a suffix graph with 2^(m-1) states, and Bernoulli pushforward measures yield closed cylinder-measure formulas where the arithmetic residue vector forms an exact m-step Markov process.",
        "scope": "Symbolic dynamics and formal language theory",
        "keywords": ["Zeckendorf expansion", "Fibonacci numeration", "shifts of finite type", "transducer theory", "Markov chains"],
        "journal": "Journal of Number Theory",
        "theorems": 68,
    },
    {
        "repo": "zeckendorf-streaming-normalization-automata-rairo",
        "title": "Canonical Zeckendorf Normalization and the Minimal Berstel Adder",
        "innovation": "The canonical low-to-high Zeckendorf normalization is non-subsequential with coordinatewise unbounded anticipation and exact prefix-destruction index Delta(n)=n, sharply contrasting the classical MSB-first Berstel adder. The Berstel transducer is proved minimal with exact state complexity 10 via kernel separation, and a linear lower bound on rounds for any fixed-radius synchronous local realization is established.",
        "scope": "Formal language theory and automata",
        "keywords": ["Zeckendorf numeration", "transducer theory", "subsequential functions", "Fibonacci addition", "state complexity"],
        "journal": "RAIRO Theoretical Informatics and Applications",
        "theorems": 44,
    },
    {
        "repo": "zero-jitter-information-clocks-parry-gibbs-rigidity",
        "title": "Tilt Dynamics of Cylinder Information and the Parry Measure on the Golden-Mean Shift",
        "innovation": "Exponential tilts of cylinder information on the golden-mean shift close within the one-step Markov family: the tilted law remains Markov with parameter satisfying a linear relation, making tilt dynamics globally linearizable. This yields a free-energy composition law, exact variance transfer, and a characterization of the Parry measure as the unique zero-jitter (constant Renyi spectrum) law. Universality of the quadratic coefficient near the Parry point is proved for all mixing SFTs.",
        "scope": "Ergodic theory and probability",
        "keywords": ["shifts of finite type", "Parry measure", "large deviations", "thermodynamic formalism", "Gibbs measures"],
        "journal": "Journal of Theoretical Probability",
        "theorems": 21,
    },
]


def gh(*args) -> subprocess.CompletedProcess:
    cmd = ["gh"] + list(args)
    return subprocess.run(cmd, capture_output=True, text=True, timeout=120)


def generate_readme(p: dict) -> str:
    title = p["title"]
    repo = p["repo"]
    journal = p["journal"]
    scope = p["scope"]
    n_thm = p["theorems"]
    innovation = p["innovation"]
    keywords = p["keywords"]
    release_base = f"https://github.com/{ORG}/{repo}/releases/download/media-v1"

    lines = [
        f"# {title}",
        "",
        " ".join([
            f"![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)",
            f"![LaTeX](https://img.shields.io/badge/Built%20with-LaTeX-008080.svg)",
            f"![Theorems](https://img.shields.io/badge/Theorems-{n_thm}-blue.svg)",
            f"![{scope}](https://img.shields.io/badge/Scope-{scope.replace(' ', '%20')}-purple.svg)",
        ]),
        "",
        f"> **Submitted to:** {journal}",
        "",
        "## Key Innovation",
        "",
        innovation,
        "",
        f"**Scope:** {scope}",
        f"**Keywords:** {', '.join(keywords)}",
        "",
        "## Presentations",
        "",
        "| Format | Link |",
        "|--------|------|",
        f"| Video | [Watch / Download]({release_base}/{repo.replace('-','_')[:40]}_video.mp4) |",
        f"| Slide Deck | [View (PDF)](media/{next((f for f in _find_media(repo)), 'slides.pdf')}) |",
        f"| Audio Podcast | [Listen / Download]({release_base}/{next((f for f in _find_audio(repo)), 'podcast.wav')}) |",
        "",
        "*Generated by [NotebookLM](https://notebooklm.google.com)*",
        "",
        "## Building",
        "",
        "```bash",
        "pdflatex main.tex && bibtex main && pdflatex main.tex && pdflatex main.tex",
        "```",
        "",
        "## Related",
        "",
        f"This paper is part of the [Omega Project](https://github.com/{ORG}/automath) "
        "-- a formalization and discovery engine for mathematics.",
        "",
        "## License",
        "",
        "MIT",
        "",
    ]
    return "\n".join(lines)


def _find_media(repo):
    """Yield slide PDF names from artifacts."""
    arts = Path(__file__).resolve().parent.parent.parent / "papers" / "publication" / "notebooklm" / "artifacts"
    for d in arts.iterdir():
        if not d.is_dir():
            continue
        for f in d.glob("*slides.pdf"):
            yield f.name
    yield "slides.pdf"


def _find_audio(repo):
    """Yield audio WAV names from artifacts."""
    arts = Path(__file__).resolve().parent.parent.parent / "papers" / "publication" / "notebooklm" / "artifacts"
    for d in arts.iterdir():
        if not d.is_dir():
            continue
        for f in d.glob("*podcast.wav"):
            yield f.name
    yield "podcast.wav"


def update_repo(p: dict, dry_run: bool = False) -> bool:
    repo = p["repo"]
    full = f"{ORG}/{repo}"

    # Get release asset names for accurate links
    rel = gh("release", "view", "media-v1", "--repo", full, "--json", "assets",
             "--jq", "[.assets[].name]")
    assets = json.loads(rel.stdout) if rel.returncode == 0 else []

    video_name = next((a for a in assets if a.endswith(".mp4")), None)
    audio_name = next((a for a in assets if a.endswith(".wav")), None)
    slides_name = next((a for a in assets if a.endswith("slides.pdf")), None)

    release_base = f"https://github.com/{full}/releases/download/media-v1"

    # Build README
    title = p["title"]
    n_thm = p["theorems"]
    scope = p["scope"]
    safe_scope = scope.replace(" ", "%20").replace("/", "%2F")

    lines = [
        f"# {title}",
        "",
        " ".join([
            f"![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)",
            f"![LaTeX](https://img.shields.io/badge/Built%20with-LaTeX-008080.svg)",
            f"![Theorems](https://img.shields.io/badge/Theorems-{n_thm}-blue.svg)",
            f"![Scope](https://img.shields.io/badge/Scope-{safe_scope}-purple.svg)",
        ]),
        "",
        f"> **Submitted to:** {p['journal']}",
        "",
        "## Key Innovation",
        "",
        p["innovation"],
        "",
        f"**Scope:** {scope}  ",
        f"**Keywords:** {', '.join(p['keywords'])}",
        "",
    ]

    # Presentations table
    lines.append("## Presentations")
    lines.append("")
    lines.append("| Format | Link |")
    lines.append("|--------|------|")
    if video_name:
        lines.append(f"| Video | [Watch / Download]({release_base}/{video_name}) |")
    if slides_name:
        lines.append(f"| Slide Deck (PDF) | [Download]({release_base}/{slides_name}) |")
    if audio_name:
        lines.append(f"| Audio Podcast | [Listen / Download]({release_base}/{audio_name}) |")
    lines.extend([
        "",
        "*Generated by [NotebookLM](https://notebooklm.google.com)*",
        "",
        "## Building",
        "",
        "```bash",
        "pdflatex main.tex && bibtex main && pdflatex main.tex && pdflatex main.tex",
        "```",
        "",
        "## Related",
        "",
        f"This paper is part of the [Omega Project](https://github.com/{ORG}/automath) "
        "-- a formalization and discovery engine for mathematics.",
        "",
        "## License",
        "",
        "MIT",
        "",
    ])

    readme = "\n".join(lines)

    if dry_run:
        print(f"[DRY RUN] {repo}")
        print(f"  Assets: video={video_name}, slides={slides_name}, audio={audio_name}")
        print(f"  README: {len(readme)} chars")
        return True

    # Clone, update README, push
    with tempfile.TemporaryDirectory() as tmp:
        clone = subprocess.run(
            ["gh", "repo", "clone", full, tmp],
            capture_output=True, text=True, timeout=60,
        )
        if clone.returncode != 0:
            print(f"  ERROR cloning: {clone.stderr.strip()[:200]}")
            return False

        readme_path = Path(tmp) / "README.md"
        readme_path.write_text(readme, encoding="utf-8")

        subprocess.run(["git", "add", "README.md"], cwd=tmp, capture_output=True)
        diff = subprocess.run(["git", "diff", "--cached", "--stat"], cwd=tmp, capture_output=True, text=True)
        if not diff.stdout.strip():
            print(f"  {repo}: no changes")
            return True

        subprocess.run(
            ["git", "commit", "-m", "Update README with innovation summary and video links"],
            cwd=tmp, capture_output=True,
        )
        push = subprocess.run(["git", "push"], cwd=tmp, capture_output=True, text=True, timeout=60)
        if push.returncode != 0:
            print(f"  ERROR pushing: {push.stderr.strip()[:200]}")
            return False

        print(f"  {repo}: README updated")
        return True


def main():
    dry_run = "--dry-run" in sys.argv
    os.environ["PATH"] = os.environ.get("PATH", "") + os.pathsep + r"C:\Program Files\GitHub CLI"

    results = []
    for p in PAPERS:
        print(f"\n{'='*60}")
        print(f"  {p['repo']}")
        ok = update_repo(p, dry_run)
        results.append((p["repo"], ok))

    print(f"\n{'='*60}")
    ok_count = sum(1 for _, ok in results if ok)
    print(f"Results: {ok_count}/{len(results)}")
    for name, ok in results:
        print(f"  [{'OK' if ok else 'FAIL'}] {name}")


if __name__ == "__main__":
    main()
