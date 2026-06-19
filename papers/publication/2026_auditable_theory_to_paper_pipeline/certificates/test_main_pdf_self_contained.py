#!/usr/bin/env python3
"""Static guard that the first compiled TeX document is self-contained."""

from __future__ import annotations

import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
MAIN_TEX = ROOT / "main.tex"


REQUIRED_FIRST_DOCUMENT_MARKERS = (
    r"V\_E = (V\_E(raw), V\_E(qrgs), V\_E(qsrc),",
    r"V\_E(qart), V\_E(qext), V\_E(qven)) in B",
    "Record type",
    "Source record",
    "Begin-token declaration",
    "Scanner row",
    "Manifest row",
    "Transcript row",
    "Promotion row",
    "Actual closure calculation",
    "finite instance",
    r"E_{\mathrm{pdf}}",
    r"E_{\mathrm{scan}}",
    r"E_{\mathrm{archive}}",
    r"E_{\mathrm{digest}}",
    r"E_{\mathrm{transcript}}",
    r"E_{\mathrm{script}}",
    r"\varnothing",
    r"\{\mathsf{raw}\}",
    r"\{\mathsf{raw},\mathsf{qrgs}\}",
    "Lemma RawScanSoundness",
    "Theorem ReplayClosure",
    "Lemma ClosedWorldExactness",
    "Related-work positioning",
)


class MainPdfSelfContainedTests(unittest.TestCase):
    def test_first_compiled_document_contains_operational_core(self) -> None:
        source = MAIN_TEX.read_text(encoding="utf-8")
        first_doc, sep, later = source.partition(r"\end{document}")
        self.assertEqual(sep, r"\end{document}")

        for marker in REQUIRED_FIRST_DOCUMENT_MARKERS:
            with self.subTest(marker=marker):
                self.assertIn(marker, first_doc)

        for marker in REQUIRED_FIRST_DOCUMENT_MARKERS:
            with self.subTest(marker=marker):
                if marker in later:
                    self.assertLess(source.index(marker), source.index(sep))


if __name__ == "__main__":
    unittest.main()
