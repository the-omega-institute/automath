# Reproducibility-statement audit across the sprint, 2026-08-19

The project charter requires, under "可复现、可审计", that every table, figure and numerical
result be script-generated and one-click reproducible, and lists a reproducibility statement
(code, script and data paths) as a required component of every paper. This audit asks a narrow
question of each sprint manuscript: does the PAPER tell a reader that the apparatus exists?

Measured over every .tex in each directory: files mentioning reproducibility, and script
filenames named in the text.

    manuscript                scripts in artifacts/   tex mentioning repro   scripts named
    window6                            18                     5                   6
    brocot                             16                     0                   1
    projection                         10                     0                   0
    scan_projection                     3                     0                   0
    cubical_stokes                      3                     0                   0
    zeck_arith                          1                     0                   0

window6 is the only one with a reproducibility section, and t454 verified that all six scripts
it names actually run and pass.

## The apparatus mostly exists; the paper does not point at it

    brocot       artifacts/REPRODUCE.md and artifacts/SHA256SUMS both present
    projection   artifacts/README.md present
    the rest     nothing

So this is not primarily a case of missing work. brocot has sixteen scripts, a REPRODUCE file
and a checksum manifest, and the manuscript names exactly one script and never uses the word
reproducibility. A referee or editor reading the paper learns none of it exists.

That is the same defect shape as the window6 abstract recorded at t445: the work was done and
the document does not say so. It costs nothing at the bench and everything at the desk.

## What this is and is not

It is a charter violation and a submission risk, five manuscripts wide.

It is NOT evidence that the scripts are broken. Only window6's were executed, at t454, and all
six passed. Whether the other papers' scripts still run is a separate question and is not
answered here; claiming otherwise would repeat the mistake of treating an unrun check as a
result.

## Action when the codex channel returns

1. Add a short reproducibility section to each of the five, naming the scripts that generate
   each displayed table and numeric claim, with paths.
2. brocot needs the least work: REPRODUCE.md and SHA256SUMS already exist and only need to be
   referenced from the manuscript.
3. Before naming any script, run it. window6's section is trustworthy because its six scripts
   were executed; a named script that no longer runs is worse than no section at all.
