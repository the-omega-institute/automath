# P5 Integration Note -- 2026-03-30

Paper: `2026_projection_ontological_mathematics_core_tams`
Target journal: Transactions of the American Mathematical Society (TAMS)
Source: P4 Editorial Review (`P4_EDITORIAL_REVIEW_2026-03-30.md`)

---

## Applied fixes

### Must-fix (blocking)

1. **$\Delta_q$ notation overload** (P4 Issue 3): The Hankel codimension in `def:resonance-polynomials` (`sec_chebotarev.tex`) was renamed from $\Delta_q := n_q - d_q$ to $\kappa_q := n_q - d_q$. All 11 downstream references within the Hankel principalization chain (Theorem, two Corollaries, and their proofs) were updated. The pressure-slope notation $\Delta_q := P_q - P_{q-1}$ in `sec_moment_kernel.tex`, `sec_introduction.tex`, `sec_conclusion.tex`, and `main.tex` is unchanged.

2. **Remark theorem style** (P4 Issue 1): In `main.tex`, the `remark` environment declaration was moved from under `\theoremstyle{plain}` to under a new `\theoremstyle{remark}` block. Remarks now render with upright body and italic header per AMS convention.

3. **Author affiliation and funding** (P4 Issue 11): Added `\address{The Omega Institute for Mathematical Research}` and `\thanks{...}` to `main.tex` to meet TAMS editorial requirements.

### Should-fix

4. **$m_0(q)$ offset discrepancy** (P4 Issue 2): In `thm:collision-kernel` (`sec_moment_kernel.tex`), the condition $m \ge m_0(q)$ with "some finite offset $m_0(q)$" was replaced by $m \ge 0$, matching the appendix proof (`prop:appendix-collision-automaton` in `sec_appendix_transducer.tex`, which proves the identity for all $m \ge 0$).

5. **Quotient variable $q$ in `prop:single-overflow`** (P4 Issue 4): In `sec_preliminaries.tex`, the quotient variable in $N_m(\omega) = qF_{m+2} + r$ was renamed from $q$ to $b$, avoiding confusion with the moment exponent $q$ used throughout the paper. This is consistent with the overflow bit $b_m(\omega) \in \{0,1\}$ already defined in the same proposition.

6. **Dangling display in `cor:visible-band`** (P4 Issue 6): In `sec_ledger.tex`, the word "Then" was inserted between the definition of $V_m(\varepsilon)$ and the concentration claim $p_m(V_m(\varepsilon)) = 1 - \exp(\cdots)$, making the corollary read as a definition followed by a claim rather than two disconnected displays.

7. **$\lambda_1 = 2$ after `thm:all-q-transfer`** (P4 Issue 7): A new `rem:lambda-one` was added in `sec_second_collision.tex` immediately after the proof of `thm:all-q-transfer`, stating: "For $q = 1$, $S_1(m) = 2^m$ gives $\lambda_1 = 2$ directly." This value enters the pressure sequence ($P_1 = \log 2$) and the Gibbs selection proof.

8. **`cor:log-density-additivity` demoted** (P4 Issue 8): In `sec_chebotarev.tex`, the corollary (with its proof) was replaced by a remark (`rem:log-density-additivity`) that states the logarithmic form of `cor:chebotarev-product` without claiming separate mathematical content.

---

## Not applied (optional per P4)

- **Issue 5** (forward reference to appendix table): No change. The forward reference already resolves after two LaTeX passes.
- **Issue 9** (`cor:renyi-rational-denominator` tangential): No change. Retained as-is.
- **Issue 10** (appendix ordering): No change needed; verified correct.
- **$q = 3, \ldots, 8$ gap remark**: Not added; the gap is documented in the P2 extension note and TRACK_BOARD.

---

## Verification

- All `.tex` files remain under 800 lines. Largest: `sec_moment_kernel.tex` at 682 lines.
- No revision-trace language in any `.tex` file.
- No `\Delta_q` remains in `sec_chebotarev.tex`; all 11 occurrences are now `\kappa_q`.
- The `\Delta_q` notation in `sec_moment_kernel.tex`, `sec_introduction.tex`, `main.tex`, and `sec_conclusion.tex` (pressure slopes) is untouched.
- The $m \ge 0$ condition in `thm:collision-kernel` now matches `prop:appendix-collision-automaton`.
- The quotient variable $b$ in `prop:single-overflow` is consistent with the overflow bit $b_m(\omega)$ defined in the same proposition.

---

## Files modified

| File | Changes |
|------|---------|
| `main.tex` | Remark theorem style; author affiliation and funding |
| `sec_moment_kernel.tex` | $m \ge 0$ in `thm:collision-kernel` |
| `sec_preliminaries.tex` | Quotient variable $q \to b$ in `prop:single-overflow` |
| `sec_ledger.tex` | "Then" connector in `cor:visible-band` |
| `sec_second_collision.tex` | New `rem:lambda-one` after `thm:all-q-transfer` |
| `sec_chebotarev.tex` | $\Delta_q \to \kappa_q$ in Hankel codimension; `cor:log-density-additivity` demoted to `rem:log-density-additivity` |
