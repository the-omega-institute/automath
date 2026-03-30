# TRACK_BOARD

Paper: *Prime languages, finite-state obstructions, and dynamical zeta-functions*
Directory: `theory/publication/2026_prime_languages_sofic_obstructions_dynamical_zeta/`

---

## Pipeline Status

| Stage | Description | Status | Date |
|---|---|---|---|
| **P0** | Intake and Contract | DONE | 2026-03-30 |
| **P1** | Traceability (SOURCE_MAP, THEOREM_LIST) | DONE | 2026-03-30 |
| **P2** | Research Extension | DONE | 2026-03-30 |
| **P3** | Proof Audit | PENDING | -- |
| **P4** | Exposition Polish | PENDING | -- |
| **P5** | Bibliography and Formatting | PENDING | -- |
| **P6** | Journal Submission Package | PENDING | -- |

---

## P0 Summary

**Title:** Prime languages, finite-state obstructions, and dynamical zeta-functions

**Subject area:** Intersection of symbolic dynamics, automata theory, combinatorics on words, and analytic number theory.

**Target journal:** *Monatshefte fur Mathematik*

**Rationale:** Short, self-contained note (8--10 pages) collecting elementary obstructions from three distinct mathematical perspectives. Monatshefte publishes clean cross-area notes at the intersection of number theory, combinatorics, and dynamics. The scope is too modest for JNT or Advances; the automata content is too light for TCS. Alternative: Proceedings of the AMS.

**MSC 2020:** 37B10, 68Q45, 11A41, 05A15

---

## P1 Summary

Artifacts produced:
- `SOURCE_MAP.md`: Enumerates all theorem-level environments across 6 .tex files.
- `THEOREM_LIST.md`: Catalogues 9 body-level claims with labels, locations, one-line statements, proof status, and dependency chain.

---

## P2 Summary

Artifact produced:
- `P2_EXTENSION_NOTE_2026-03-30.md`

Key findings:
- Results range from folklore to mild extensions of standard material. The value is in the systematic assembly.
- The density dichotomy (Block A) is standard finite Markov chain theory; the DFA application to primes is a clean new formulation.
- The Zeckendorf argument (Block B) generalizes to all Parry numeration systems; this generality should be stated.
- The natural boundary proof (Block C, Thm 8) is too terse and needs a non-cancellation clarification.
- Proposition 9 implicitly uses irrationality of $\log 2$ without stating it.
- The bibliography contains 12+ uncited entries from the parent manuscript and is missing key references (Allouche--Shallit, Cobham, Hardy--Wright, Bruyere--Hansel, Flajolet--Sedgewick).
- No computational/reproducibility component; the paper is purely theoretical.

---

## Pending stages

**P3 (Proof Audit):** Line-by-line verification of all 9 claims. Priority items: natural boundary non-cancellation argument, $\lambda = 0$ edge case in Zeckendorf theorem, leading-zeros convention in DFA corollaries.

**P4 (Exposition Polish):** Label the unlabelled DFA definition; define $\mathrm{val}(w)$ before first use in introduction; state Parry-numeration generality; make the $\log 2$ irrationality explicit.

**P5 (Bibliography and Formatting):** Remove uncited entries; add Allouche--Shallit, Hardy--Wright, Bruyere--Hansel, Cobham, Mauduit--Rivat, Estermann, Flajolet--Sedgewick, Frougny. Verify amsart formatting for Monatshefte submission.

**P6 (Journal Submission Package):** Prepare cover letter, compile PDF, verify MSC codes, finalize author metadata.
