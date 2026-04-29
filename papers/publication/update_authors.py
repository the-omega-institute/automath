#!/usr/bin/env python3
"""Update author metadata in all papers to standardized format."""
import re
from pathlib import Path

ARTICLE_AUTHORS = (
    "\\author{\n"
    "  Haobo Ma\\thanks{AELF PTE LTD., \\#14-02, Marina Bay Financial Centre Tower 1, "
    "8 Marina Blvd, Singapore 018981. Email: \\texttt{auric@aelf.io}}\n"
    "  \\and\n"
    "  Wenlin Zhang\\thanks{Corresponding author. National University of Singapore, "
    "Singapore. Email: \\texttt{e1327962@u.nus.edu}}\n"
    "}\n\\date{}"
)

AMSART_AUTHORS = (
    "\\author{Haobo Ma}\n"
    "\\address[Haobo Ma]{AELF PTE LTD., \\#14-02, Marina Bay Financial Centre Tower 1, "
    "8 Marina Blvd, Singapore 018981}\n"
    "\\email[Haobo Ma]{auric@aelf.io}\n\n"
    "\\author{Wenlin Zhang}\n"
    "\\address[Wenlin Zhang]{National University of Singapore, Singapore}\n"
    "\\email[Wenlin Zhang]{e1327962@u.nus.edu}"
)

count = 0
base = Path(__file__).parent

for d in sorted(base.glob("2026_*/")):
    main = d / "main.tex"
    if not main.exists():
        continue
    text = main.read_text(encoding="utf-8", errors="replace")
    original = text
    is_ams = "amsart" in text[:200] or "{tac}" in text[:200]

    # Remove \thanks{...acknowledge...}
    text = re.sub(r"\\thanks\{[^}]*acknowledge[^}]*\}", "", text, flags=re.IGNORECASE)

    if is_ams:
        # amsart/tac: replace \author{...} block including \address, \email lines
        text = re.sub(
            r"\\author\{[^}]*\}(?:\s*\\(?:address|email|curraddr|urladdr)(?:\[[^\]]*\])?\{[^}]*\})*",
            lambda m: AMSART_AUTHORS,
            text, count=1, flags=re.DOTALL,
        )
    else:
        # article: replace \author{...} possibly with nested braces, and \date{...}
        text = re.sub(
            r"\\author\{.*?\}(?:\s*\\date\{[^}]*\})?",
            lambda m: ARTICLE_AUTHORS,
            text, count=1, flags=re.DOTALL,
        )

    if text != original:
        main.write_text(text, encoding="utf-8")
        count += 1
        print(f"Updated: {d.name}")
    else:
        print(f"No change: {d.name}")

print(f"\nDone: {count} papers updated")
