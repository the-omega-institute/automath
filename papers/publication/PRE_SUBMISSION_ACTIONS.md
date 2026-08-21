# Pre-submission action list

## STATUS as of t542: one item is open. A submission-materials audit found it.

OPEN: window6 declares no 2020 MSC codes and no keywords. Its own checklist recorded both as NOT
MET and that record is correct -- main.tex uses \documentclass{article}, so it has no \subjclass
macro and nothing supplies them. The primary target, The Electronic Journal of Combinatorics,
prints MSC classifications with the article. A fix is in flight (t542).

The audit that found it also found the reverse problem, which is worth stating because it
changes how much these files can be trusted. scan_projection's checklist carried a FAIL saying
uthor{} is empty; both authors are in fact declared with affiliations and emails and the PDF
front page renders both names, so the FAIL was stale. The same checklist recorded a page count
of about 35 as a PASS, derived by scaling source line counts, against a real build of 18 pages.
A checklist can therefore be wrong in both directions at once: it can block a submittable paper
and it can pass a number nobody measured. Both lines are corrected.

Not defects, checked and dismissed this tick: cubical_stokes has 3 unused bibliography entries
with zero missing keys, which is harmless; the brocot and cubical_stokes abstract word counts
are marked NOT CHECKED rather than over any stated limit; and window6's page count differs by
engine, which both of its files already state explicitly.

A referee-style cold read at t537 found three real defects in zeck_arith, two of them in text I
had verified and committed at t526: the abstract stated the multiplication-delay bound with no
hypothesis where the theorem requires n >= 3 and a specific scan model, the abstract promised
Chinese-remainder decompositions for any composite modulus where the body's own trichotomy makes
a prime power local and non-splitting, and the cover letter asserted a submission ordering the
repository cannot support. All three are fixed and independently checked (t538, commit 474526666):
rebuild from zero, exit 0, 34 pages, both corrected phrases confirmed in the extracted PDF text.

The lesson is worth keeping. My t526 checks were mechanical -- does it build, were theorems
touched, do assertions match the repository -- and finding these required aligning every
quantifier in the abstract against the body sentence by sentence. Mechanical verification has a
definite blind spot around exactly that.

All 47 verify_* scripts across the six manuscripts were re-run at t538 with an
output-non-empty control: 47 pass, 0 silent, 0 timeout, and the one non-zero exit is brocot's
deliberately excluded NOT DISCRIMINATING script.

All six sprint manuscripts now carry a PDF, a cover letter, submission metadata, a submission
checklist and a reproducibility statement. Verified state, with the tick where each was checked:

    window6          clean build t533, 6 named scripts pass t454, abstract retitled t524
    projection       clean build t530, 10 named scripts pass t530, attribution fixed t525
    brocot           clean build t530, 15 named scripts pass t530, constant confirmed t473
    zeck_arith       clean build t526, 1 named script passes t526, materials created t526
    scan_projection  clean build t530, 2 named scripts pass t530, abstract clean t447
    cubical_stokes   clean build t530, 3 named scripts pass t530, abstract exemplary t447

Thirty named scripts were executed independently at t530: 30 passed, 0 failed.

NOTHING IS OPEN. The last item, brocot's target journal, was settled on 2026-08-21: TAMS is
confirmed, with Journal of Number Theory as fallback, and the AIHP proposal was declined. The
cover letter and submission_metadata.md already agreed on TAMS, so no edits were needed. The
decision is recorded in that paper's submission_metadata.md so the stale AIHP note cannot
reopen it.

Everything below is the record of how these items were found and closed.

---

Digest of what this sprint window established, one section per manuscript, ordered by what
blocks submission. The board is a chronological log and is now too long to act from; this is
the actionable extract. Every item cites the tick where it was established so the evidence can
be found.

Nothing here is a writing task I performed. Items marked WRITING need the codex channel.

---

## window6 — blocking defect CLOSED (t524)

**BLOCKING, WRITING.** The title and abstract still describe the desk-rejected scope (t445).
The referee rejected it for treating one 64-vertex graph and asked for a family. The body was
extended: the introduction defines Fold_m and the involutions for general m, and a proposition
pins the involution-admissible dimensions to {3, 6, 8, 9} via the imported Bugeaud-Cipu-
Mignotte theorem. The cover letter was also rewritten and mentions family, classification and
sporadic three times (t462). Only the title and abstract were left behind, and those are what
a desk decision is made on. Actionable now: the classification does not depend on any unproved
lemma.

**WRITING.** Bibliography has five entries, and the manuscript never uses "perfect colouring",
the name this object carries in the school that has done most of the hypercube work
(Fon-Der-Flaass, Avgustinovich, Vasil'eva, Solov'eva). A referee from that community will search
the term, miss it, and conclude the field was unread (t440).

**Not defects, recorded to prevent rework.** The sporadic set is {3, 6, 8, 9}; the paper was
right and my reconstruction was wrong (t442), confirmed independently by the paper's own
verify_refinement_family.py (t454). The reproducibility section is sound and all six named
scripts run and pass (t454). Priority checked with a working control: no collision (t440).

**Beyond the manuscript.** The two-star lemma is now verified for 6 <= m <= 5000, and the
ineffective Subspace step has been replaced by an effective route with an explicit cutoff at
m >= 17, resting on one remaining arithmetic proposition (t436-t453). None of this is in the
paper. If any of it is promoted, the corresponding scripts must be named in the reproducibility
section at the same time.

---

## projection — attribution CLOSED (t525)

**BLOCKING, WRITING.** The abstract says a finite-state kernel "identifies each lambda_q as the
Perron root of a nonnegative integer matrix and hence proves that lambda_q is an algebraic
integer". That is Sanna's Theorem 1, by Sanna's method (t430, verified by reading
arXiv:2309.12724v2 rather than its abstract). He is cited elsewhere so the overlap is not
concealed, but a referee who knows the paper will read that sentence as claiming his result.

**WRITING.** The polynomials for q = 9..17 extend Sanna's Table 1, which stops at p = 8, and
must be presented as an extension (t430). The Galois determination should not be framed as
surprising: his own eight rows are also fully symmetric (t431).

**Template.** cubical_stokes solves exactly this problem in its own abstract, naming its
principal contribution and then saying which components are standard. Use that shape (t447).

---

## brocot — one unsettled claim, one venue decision

**RESOLVED (t473).** The headline constant is 8, confirmed by independent computation. The
transfer-operator route that t459 identified as necessary was supplied by the Oracle as a
resolvent recurrence; I implemented it, validated it against my exact-integer table to 1e-14,
and computed Z_n to n = 1000. The sequence peaks at 15.276 near n = 27 and descends to 8.2186
at n = 1000, so C = 2R_s^2 = 8 and the published 10 is wrong, which is what the paper claims.
The error mechanism was separately verified at t460. Nothing further is needed here.

**DECISION NEEDED, NOT MINE.** The cover letter addresses TAMS and submission_metadata.md
records TAMS as primary with JNT fallback, so the two agree. An earlier note called for
retargeting to AIHP. That conflict is a venue choice, not a defect (t462).

**Fixed.** verify_dushistova_coefficient.py was emitting "the data favour: Dushistova" with
exit 1; replaced by an explicit NOT DISCRIMINATING report (t456).

**WRITING.** No reproducibility statement, though artifacts/REPRODUCE.md and
artifacts/SHA256SUMS both exist and only need referencing (t455). Two scripts assume the paper
root as working directory and fail from inside artifacts/ (t456).

---

## zeck_arith — submission materials CLOSED (t526)

**BLOCKING, WRITING.** The only sprint manuscript with no cover letter, no checklist and no
metadata (t462). Target is on record: Integers, Electronic Journal of Combinatorial Number
Theory, per scope_contract.md. A full brief is assembled at
artifacts/submission_brief_2026-08-19.md (t463) covering what the letter must lead with, the
venue tension, the disclosures and the citations.

**BLOCKING, WRITING.** The sibling manuscript ITA-2026-0032 is before referees at RAIRO ITA on
the Berstel adder; Section 7 here builds an online addition transducer and mentions Berstel
zero times (t434). Two overlapping submissions from the same authors must cite each other.

**WRITING.** Three verified-missing citations: Labbe-Lepsova 2023, Fenwick 2003,
Dimitrov-Donevsky 1995 (t434). None threatens priority; Fenwick is the conspicuous one.

---

## scan_projection and cubical_stokes — clean

Both abstracts state their central claims accurately (t447), and cubical_stokes is the model
for disclosure. Central claims verified independently: the period-two phase-dependence (t435)
and the box extremal value (earlier). Both lack a reproducibility statement (t455).

---

## Sprint-wide

**CLOSED (t530).** All six manuscripts now carry a reproducibility statement. zeck_arith
gained one at t526 and the remaining four at t530, naming 30 scripts between them. Every named
script was executed independently and all 30 pass; all four papers rebuild clean from
latexmk -C. The exclusions are deliberate: brocot leaves out its three test_* files and
verify_dushistova_coefficient.py, which exits 2 with an explicit NOT DISCRIMINATING report.

**Method note for whoever continues.** Exit codes are not results. At t456 I logged 30 of 33
scripts as OK from status alone; two of them print material that changes the conclusion, and I
spent three ticks re-deriving something a docstring already said (t460). Read the output.
