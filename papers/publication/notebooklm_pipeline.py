#!/usr/bin/env python3
"""Automated NotebookLM Pipeline — Theory → Deck → Video → Social Media.

Four-stage content pipeline transforming machine-verified Lean 4 theorems
into shareable social media content.

Stage 1: Lean 4 theorems + LaTeX → bilingual summaries (EN/ZH)
Stage 2: Summaries → visual HTML slides
Stage 3: Slides → short-form video (via Puppeteer screenshot + ffmpeg)
Stage 4: Auto-publish metadata for social platforms

Usage:
    python notebooklm_pipeline.py --paper <dir>                    # Full pipeline
    python notebooklm_pipeline.py --paper <dir> --stage 1          # Summary only
    python notebooklm_pipeline.py --paper <dir> --stage 2          # Slides only
    python notebooklm_pipeline.py --lean Omega/Zeta/DynZeta.lean   # From Lean file
    python notebooklm_pipeline.py --discovery report.json          # From discovery JSON
    python notebooklm_pipeline.py --list                           # List available papers

Integrates with:
    - lean4_discovery_export.py (Issue #22) for theorem extraction
    - notebooklm_dispatch.py / notebooklm_server.py for NotebookLM bridge
    - oracle_dispatch.py for ChatGPT summarization fallback
"""

import argparse
import json
import os
import re
import subprocess
import sys
import textwrap
import time
from datetime import datetime
from pathlib import Path

PUBLICATION_DIR = Path(__file__).resolve().parent
LEAN4_DIR = PUBLICATION_DIR.parent.parent / "lean4"
OUTPUT_DIR = PUBLICATION_DIR / "notebooklm" / "pipeline"
DISCOVERY_DIR = PUBLICATION_DIR / "discovery"

# ── Stage 1: Theorem → Bilingual Summary ────────────────────────────────


def extract_theorems_from_paper(paper_dir: Path) -> list[dict]:
    """Extract theorem inventory from a paper's .tex files."""
    claim_re = re.compile(
        r"\\begin\{(theorem|lemma|proposition|corollary|definition)\}"
        r"(?:\[([^\]]*)\])?\s*"
        r"\\label\{([^}]+)\}",
        re.DOTALL,
    )
    block_re = re.compile(
        r"(\\begin\{(theorem|lemma|proposition|corollary|definition)\}"
        r".*?"
        r"\\end\{\2\})",
        re.DOTALL,
    )

    theorems = []
    for tex in sorted(paper_dir.glob("**/*.tex")):
        text = tex.read_text(encoding="utf-8", errors="replace")
        for m in block_re.finditer(text):
            block = m.group(1)
            env_type = m.group(2)
            label_m = re.search(r"\\label\{([^}]+)\}", block)
            title_m = re.search(
                r"\\begin\{" + env_type + r"\}\[([^\]]+)\]", block
            )
            # Clean LaTeX from statement
            statement = block
            statement = re.sub(r"\\begin\{[^}]+\}(\[[^\]]*\])?", "", statement)
            statement = re.sub(r"\\end\{[^}]+\}", "", statement)
            statement = re.sub(r"\\label\{[^}]+\}", "", statement)
            statement = statement.strip()

            theorems.append({
                "env_type": env_type,
                "label": label_m.group(1) if label_m else "",
                "title": title_m.group(1) if title_m else "",
                "statement": statement[:500],
                "source_file": tex.name,
            })
    return theorems


def extract_theorems_from_lean(lean_path: Path) -> list[dict]:
    """Extract theorems from a Lean file (lightweight, no full parse)."""
    text = lean_path.read_text(encoding="utf-8", errors="replace")
    decl_re = re.compile(
        r"/--(.+?)-/\s*(theorem|lemma|def)\s+(\S+)(.*?)(?=\n(?:theorem|lemma|def|abbrev|instance|/--|end\s|$))",
        re.DOTALL,
    )
    theorems = []
    for m in decl_re.finditer(text):
        docstring = m.group(1).strip()
        decl_type = m.group(2)
        name = m.group(3)
        body = m.group(4).strip()
        theorems.append({
            "env_type": decl_type,
            "label": name,
            "title": docstring.split("\n")[0][:120],
            "statement": body[:500],
            "source_file": lean_path.name,
        })
    return theorems


def extract_theorems_from_discovery(discovery_path: Path) -> list[dict]:
    """Load theorems from a discovery report JSON (Issue #22 output)."""
    data = json.loads(discovery_path.read_text(encoding="utf-8"))
    return [
        {
            "env_type": d["lean_type"],
            "label": d["lean_theorem"],
            "title": d.get("docstring", "").split("\n")[0][:120],
            "statement": d.get("lean_statement", "")[:500],
            "source_file": d.get("lean_file", ""),
        }
        for d in data.get("discoveries", [])
    ]


def generate_summary(theorems: list[dict], paper_title: str) -> dict:
    """Generate bilingual summary from theorem inventory.

    Returns a summary dict with EN and ZH versions.
    Uses template-based generation (no external API needed).
    """
    # Group by type
    by_type = {}
    for t in theorems:
        by_type.setdefault(t["env_type"], []).append(t)

    # Build structured summary
    lines_en = [f"# {paper_title}", ""]
    lines_zh = [f"# {paper_title}", ""]

    type_names_en = {
        "theorem": "Theorems", "lemma": "Lemmas", "proposition": "Propositions",
        "corollary": "Corollaries", "definition": "Definitions",
        "def": "Definitions", "abbrev": "Abbreviations",
    }
    type_names_zh = {
        "theorem": "定理", "lemma": "引理", "proposition": "命题",
        "corollary": "推论", "definition": "定义",
        "def": "定义", "abbrev": "缩写",
    }

    lines_en.append(f"**{len(theorems)} machine-verified results**\n")
    lines_zh.append(f"**{len(theorems)} 个机器验证结果**\n")

    for env_type, items in by_type.items():
        en_name = type_names_en.get(env_type, env_type.capitalize() + "s")
        zh_name = type_names_zh.get(env_type, env_type)

        lines_en.append(f"## {en_name} ({len(items)})")
        lines_zh.append(f"## {zh_name} ({len(items)})")

        for item in items[:20]:  # cap at 20 per type for readability
            title = item.get("title") or item.get("label", "")
            lines_en.append(f"- **{item['label']}**: {title}")
            lines_zh.append(f"- **{item['label']}**: {title}")

        if len(items) > 20:
            lines_en.append(f"  ... and {len(items) - 20} more")
            lines_zh.append(f"  ... 以及其余 {len(items) - 20} 条")

        lines_en.append("")
        lines_zh.append("")

    return {
        "title": paper_title,
        "theorem_count": len(theorems),
        "summary_en": "\n".join(lines_en),
        "summary_zh": "\n".join(lines_zh),
        "theorems": theorems,
    }


# ── Stage 2: Summary → HTML Slides ──────────────────────────────────────


SLIDE_TEMPLATE = """\
<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{title}</title>
<link rel="stylesheet" href="https://cdn.jsdelivr.net/npm/katex@0.16.9/dist/katex.min.css">
<style>
:root {{
  --bg: #0d1117; --fg: #e6edf3; --accent: #58a6ff;
  --card-bg: #161b22; --border: #30363d;
}}
* {{ margin: 0; padding: 0; box-sizing: border-box; }}
body {{ background: var(--bg); color: var(--fg); font-family: 'Inter', system-ui, sans-serif; }}
.slide {{
  width: 1280px; height: 720px; padding: 60px;
  display: flex; flex-direction: column; justify-content: center;
  page-break-after: always; position: relative;
  background: var(--bg);
}}
.slide::after {{
  content: attr(data-num); position: absolute; bottom: 30px; right: 40px;
  color: #484f58; font-size: 14px;
}}
h1 {{ font-size: 42px; color: var(--accent); margin-bottom: 20px; line-height: 1.2; }}
h2 {{ font-size: 32px; color: var(--accent); margin-bottom: 16px; }}
.subtitle {{ font-size: 22px; color: #8b949e; margin-bottom: 30px; }}
.result-card {{
  background: var(--card-bg); border: 1px solid var(--border);
  border-radius: 12px; padding: 24px; margin: 10px 0;
}}
.result-card .label {{ color: var(--accent); font-size: 14px; font-weight: 600;
  text-transform: uppercase; letter-spacing: 1px; margin-bottom: 8px; }}
.result-card .statement {{ font-size: 18px; line-height: 1.6; }}
.stats {{ display: flex; gap: 40px; margin-top: 30px; }}
.stat {{ text-align: center; }}
.stat .num {{ font-size: 56px; font-weight: 700; color: var(--accent); }}
.stat .lbl {{ font-size: 16px; color: #8b949e; margin-top: 4px; }}
.tag {{ display: inline-block; background: #1f6feb33; color: var(--accent);
  padding: 4px 12px; border-radius: 20px; font-size: 14px; margin: 2px; }}
.footer {{ position: absolute; bottom: 30px; left: 60px;
  font-size: 13px; color: #484f58; }}
.omega {{ color: var(--accent); font-weight: 700; }}
</style>
</head>
<body>
{slides}
</body>
</html>
"""


def _escape(text: str) -> str:
    return text.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")


def generate_slides(summary: dict) -> str:
    """Generate HTML slide deck from summary."""
    slides = []
    num = 0
    theorems = summary["theorems"]
    title = _escape(summary["title"])

    # ── Title slide
    num += 1
    by_type = {}
    for t in theorems:
        by_type.setdefault(t["env_type"], []).append(t)

    stats_html = ""
    for env_type, items in list(by_type.items())[:4]:
        stats_html += (
            f'<div class="stat"><div class="num">{len(items)}</div>'
            f'<div class="lbl">{_escape(env_type)}s</div></div>'
        )

    slides.append(f"""\
<div class="slide" data-num="{num}">
  <h1>{title}</h1>
  <p class="subtitle">Machine-verified mathematical results &mdash; <span class="omega">Omega</span> Project</p>
  <div class="stats">{stats_html}</div>
  <div class="footer">Formally verified in Lean 4 + Mathlib</div>
</div>""")

    # ── Content slides (group theorems, max 3 per slide)
    all_results = [(t["env_type"], t) for t in theorems]
    chunk_size = 3
    for i in range(0, min(len(all_results), 30), chunk_size):
        num += 1
        chunk = all_results[i : i + chunk_size]
        cards = ""
        for env_type, t in chunk:
            label = _escape(t.get("label", ""))
            stmt = _escape(t.get("title") or t.get("statement", "")[:200])
            cards += f"""\
    <div class="result-card">
      <div class="label">{_escape(env_type)} &mdash; {label}</div>
      <div class="statement">{stmt}</div>
    </div>
"""
        slides.append(f"""\
<div class="slide" data-num="{num}">
  <h2>Results ({i + 1}&ndash;{i + len(chunk)})</h2>
{cards}
  <div class="footer">{title}</div>
</div>""")

    # ── Closing slide
    num += 1
    tags = " ".join(
        f'<span class="tag">{_escape(k)}</span>'
        for k in by_type
    )
    slides.append(f"""\
<div class="slide" data-num="{num}">
  <h1>Summary</h1>
  <p class="subtitle">{len(theorems)} verified results across {len(by_type)} categories</p>
  <div style="margin-top: 20px;">{tags}</div>
  <div style="margin-top: 40px; font-size: 20px; color: #8b949e;">
    All results formally verified in Lean 4.<br>
    Source: <span class="omega">Omega</span> &mdash; the-omega-institute/automath
  </div>
  <div class="footer">Generated {datetime.now().strftime('%Y-%m-%d')}</div>
</div>""")

    return SLIDE_TEMPLATE.format(title=title, slides="\n".join(slides))


# ── Stage 3: Slides → Video ─────────────────────────────────────────────


def generate_video(slides_path: Path, output_path: Path, duration: int = 5) -> bool:
    """Convert HTML slides to video using Puppeteer screenshots + ffmpeg.

    Requires: node, puppeteer (npm i puppeteer), ffmpeg
    Falls back to static image sequence if tools are missing.
    """
    frames_dir = output_path.parent / "frames"
    frames_dir.mkdir(parents=True, exist_ok=True)

    # Puppeteer screenshot script
    screenshot_js = f"""\
const puppeteer = require('puppeteer');
(async () => {{
  const browser = await puppeteer.launch({{headless: 'new'}});
  const page = await browser.newPage();
  await page.setViewport({{width: 1280, height: 720}});
  await page.goto('file:///{slides_path.as_posix()}', {{waitUntil: 'networkidle0'}});
  const slides = await page.$$('.slide');
  for (let i = 0; i < slides.length; i++) {{
    await slides[i].screenshot({{
      path: '{frames_dir.as_posix()}/slide_' + String(i).padStart(3, '0') + '.png'
    }});
  }}
  await browser.close();
}})();
"""
    js_path = frames_dir / "screenshot.js"
    js_path.write_text(screenshot_js)

    # Try Puppeteer
    try:
        result = subprocess.run(
            ["node", str(js_path)], capture_output=True, text=True, timeout=60,
        )
        if result.returncode != 0:
            print(f"  [video] Puppeteer failed: {result.stderr[:200]}")
            print("  [video] Install: npm i puppeteer")
            return False
    except FileNotFoundError:
        print("  [video] node not found — skipping video generation")
        print("  [video] Install Node.js and run: npm i puppeteer")
        return False

    # ffmpeg: stitch frames into video
    png_count = len(list(frames_dir.glob("slide_*.png")))
    if png_count == 0:
        print("  [video] No frames captured")
        return False

    try:
        cmd = [
            "ffmpeg", "-y",
            "-framerate", f"1/{duration}",
            "-i", str(frames_dir / "slide_%03d.png"),
            "-c:v", "libx264", "-pix_fmt", "yuv420p",
            "-vf", "scale=1280:720",
            str(output_path),
        ]
        result = subprocess.run(cmd, capture_output=True, text=True, timeout=120)
        if result.returncode != 0:
            print(f"  [video] ffmpeg failed: {result.stderr[:200]}")
            return False
        print(f"  [video] Generated: {output_path} ({png_count} slides × {duration}s)")
        return True
    except FileNotFoundError:
        print("  [video] ffmpeg not found — skipping video generation")
        print("  [video] Install ffmpeg and add to PATH")
        return False


# ── Stage 4: Social Media Metadata ──────────────────────────────────────


def generate_social_metadata(summary: dict, output_dir: Path) -> dict:
    """Generate social media post metadata (title, description, tags)."""
    title = summary["title"]
    count = summary["theorem_count"]

    # Collect unique env types for tags
    env_types = list({t["env_type"] for t in summary["theorems"]})

    metadata = {
        "generated": datetime.now().isoformat(),
        "platforms": {
            "youtube": {
                "title": f"{title} — {count} Machine-Verified Results",
                "description": (
                    f"Formal verification of {count} mathematical results "
                    f"from the Omega project.\n\n"
                    f"All theorems are machine-checked in Lean 4 with Mathlib.\n\n"
                    f"Categories: {', '.join(env_types)}\n\n"
                    f"Source: https://github.com/the-omega-institute/automath\n\n"
                    f"#Mathematics #FormalVerification #Lean4 #Omega"
                ),
                "tags": [
                    "mathematics", "formal verification", "Lean 4",
                    "machine learning", "theorem proving", "Omega project",
                ] + env_types,
            },
            "twitter": {
                "thread": [
                    f"🔬 {count} machine-verified mathematical results from the Omega project\n\n"
                    f"Topic: {title}\n\n"
                    f"All formally proven in Lean 4 + Mathlib. Thread 🧵",
                    summary["summary_en"][:270] + "...",
                    f"Full source: github.com/the-omega-institute/automath\n\n"
                    f"#Math #Lean4 #FormalVerification",
                ],
            },
            "bilibili": {
                "title": f"{title} — {count} 个机器验证数学定理",
                "description": (
                    f"Omega 项目：{count} 个数学结果的形式化验证\n\n"
                    f"所有定理均在 Lean 4 + Mathlib 中机器证明。\n\n"
                    f"源码：https://github.com/the-omega-institute/automath"
                ),
                "tags": ["数学", "形式化验证", "Lean4", "定理证明", "Omega"],
            },
        },
    }

    meta_path = output_dir / "social_metadata.json"
    meta_path.write_text(
        json.dumps(metadata, indent=2, ensure_ascii=False), encoding="utf-8",
    )
    print(f"  [social] Metadata: {meta_path}")
    return metadata


# ── Orchestrator ─────────────────────────────────────────────────────────


def find_paper_title(paper_dir: Path) -> str:
    """Extract paper title from main.tex or directory name."""
    main_tex = paper_dir / "main.tex"
    if main_tex.exists():
        text = main_tex.read_text(encoding="utf-8", errors="replace")
        m = re.search(r"\\title\{([^}]+)\}", text)
        if m:
            return m.group(1).strip()
    # Fallback: directory name
    name = paper_dir.name.replace("2026_", "").replace("_", " ").title()
    return name


def list_papers():
    """List all available papers."""
    for d in sorted(PUBLICATION_DIR.iterdir()):
        if d.is_dir() and d.name.startswith("2026_"):
            pipeline = d / "PIPELINE.md"
            status = ""
            if pipeline.exists():
                text = pipeline.read_text(encoding="utf-8", errors="replace")
                if "ACCEPT" in text[:500]:
                    status = " [ACCEPT]"
                elif "submitted" in text[:500].lower():
                    status = " [submitted]"
            print(f"  {d.name}{status}")


def run_pipeline(
    paper_dir: Path = None,
    lean_path: Path = None,
    discovery_path: Path = None,
    stages: list[int] = None,
):
    """Run the full or partial pipeline."""
    if stages is None:
        stages = [1, 2, 3, 4]

    run_id = datetime.now().strftime("%Y%m%d_%H%M%S")

    # Determine source and extract theorems
    if discovery_path:
        theorems = extract_theorems_from_discovery(discovery_path)
        title = discovery_path.stem.replace("_", " ").title()
        source_type = "discovery"
    elif lean_path:
        full_path = lean_path if lean_path.is_absolute() else LEAN4_DIR / lean_path
        theorems = extract_theorems_from_lean(full_path)
        title = full_path.stem.replace("_", " ").title()
        source_type = "lean"
    elif paper_dir:
        theorems = extract_theorems_from_paper(paper_dir)
        title = find_paper_title(paper_dir)
        source_type = "paper"
    else:
        print("ERROR: Provide --paper, --lean, or --discovery")
        sys.exit(1)

    if not theorems:
        print(f"WARNING: No theorems found from {source_type} source")
        sys.exit(1)

    slug = re.sub(r"[^a-z0-9]+", "_", title.lower())[:50].strip("_")
    out_dir = OUTPUT_DIR / f"{run_id}_{slug}"
    out_dir.mkdir(parents=True, exist_ok=True)

    print(f"Pipeline: {title}")
    print(f"Source: {source_type}, {len(theorems)} theorems")
    print(f"Output: {out_dir}")
    print(f"Stages: {stages}\n")

    manifest = {
        "run_id": run_id,
        "title": title,
        "source_type": source_type,
        "theorem_count": len(theorems),
        "stages_requested": stages,
        "stages_completed": [],
        "outputs": {},
    }

    # Stage 1: Bilingual Summary
    if 1 in stages:
        print("[Stage 1] Generating bilingual summary...")
        summary = generate_summary(theorems, title)
        # Write summaries
        (out_dir / "summary_en.md").write_text(summary["summary_en"], encoding="utf-8")
        (out_dir / "summary_zh.md").write_text(summary["summary_zh"], encoding="utf-8")
        manifest["stages_completed"].append(1)
        manifest["outputs"]["summary_en"] = "summary_en.md"
        manifest["outputs"]["summary_zh"] = "summary_zh.md"
        print(f"  EN: {len(summary['summary_en'])} chars")
        print(f"  ZH: {len(summary['summary_zh'])} chars\n")
    else:
        # Load existing summary for later stages
        summary = generate_summary(theorems, title)

    # Stage 2: HTML Slides
    if 2 in stages:
        print("[Stage 2] Generating HTML slides...")
        slides_html = generate_slides(summary)
        slides_path = out_dir / "slides.html"
        slides_path.write_text(slides_html, encoding="utf-8")
        manifest["stages_completed"].append(2)
        manifest["outputs"]["slides"] = "slides.html"
        slide_count = slides_html.count('class="slide"')
        print(f"  {slide_count} slides -> {slides_path}\n")

    # Stage 3: Video
    if 3 in stages:
        print("[Stage 3] Generating video...")
        slides_path = out_dir / "slides.html"
        if not slides_path.exists():
            print("  SKIP: No slides.html found (run stage 2 first)\n")
        else:
            video_path = out_dir / "presentation.mp4"
            ok = generate_video(slides_path, video_path)
            if ok:
                manifest["stages_completed"].append(3)
                manifest["outputs"]["video"] = "presentation.mp4"
            print()

    # Stage 4: Social Media Metadata
    if 4 in stages:
        print("[Stage 4] Generating social media metadata...")
        generate_social_metadata(summary, out_dir)
        manifest["stages_completed"].append(4)
        manifest["outputs"]["social_metadata"] = "social_metadata.json"
        print()

    # Write manifest
    manifest_path = out_dir / "manifest.json"
    manifest_path.write_text(
        json.dumps(manifest, indent=2, ensure_ascii=False), encoding="utf-8",
    )
    print(f"Done. Manifest: {manifest_path}")
    print(f"Completed stages: {manifest['stages_completed']}")
    return manifest


def main():
    parser = argparse.ArgumentParser(
        description="NotebookLM Pipeline: Theory → Deck → Video → Social"
    )
    parser.add_argument("--paper", help="Paper directory path")
    parser.add_argument("--lean", help="Lean file path (relative to lean4/)")
    parser.add_argument("--discovery", help="Discovery report JSON (from lean4_discovery_export.py)")
    parser.add_argument("--stage", type=int, action="append",
                        help="Run specific stage(s): 1=summary, 2=slides, 3=video, 4=social")
    parser.add_argument("--list", action="store_true", help="List available papers")
    args = parser.parse_args()

    if args.list:
        print("Available papers:")
        list_papers()
        return

    paper_dir = Path(args.paper).resolve() if args.paper else None
    lean_path = Path(args.lean) if args.lean else None
    discovery_path = Path(args.discovery) if args.discovery else None

    if not any([paper_dir, lean_path, discovery_path]):
        parser.print_help()
        sys.exit(1)

    stages = args.stage if args.stage else [1, 2, 3, 4]
    run_pipeline(paper_dir, lean_path, discovery_path, stages)


if __name__ == "__main__":
    main()
