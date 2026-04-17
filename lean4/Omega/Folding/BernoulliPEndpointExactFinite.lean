import Mathlib.Tactic

namespace Omega.Folding

/-- The zero-mismatch closed form from the `{a,d}` transfer-matrix diagonalization. -/
def zeroMismatchClosedForm (CPlus CMinus lambdaPlus lambdaMinus : ℚ) (m : ℕ) : ℚ :=
  CPlus * lambdaPlus ^ m + CMinus * lambdaMinus ^ m

/-- The residue-dependent prefactor for the full-mismatch `a → b → c → a` cycle. -/
def fullMismatchResidueValue (u0 u1 u2 : ℚ) (r : ℕ) : ℚ :=
  if r = 0 then u0 else if r = 1 then u1 else u2

/-- Paper-facing wrapper for the finite-length endpoint formulas:
    zero mismatch is governed by a two-root closed form, while full mismatch is
    forced onto the unique 3-cycle and therefore splits by `m mod 3`.
    thm:fold-bernoulli-p-endpoint-exact-finite -/
theorem paper_fold_bernoulli_p_endpoint_exact_finite
    (zeroMismatch fullMismatch : ℕ → ℚ)
    (lambdaPlus lambdaMinus CPlus CMinus t z0 z1 u0 u1 u2 : ℚ)
    (hZero : ∀ m, 2 ≤ m →
      zeroMismatch m = zeroMismatchClosedForm CPlus CMinus lambdaPlus lambdaMinus m)
    (hZero0 : zeroMismatch 0 = z0)
    (hZero1 : zeroMismatch 1 = z1)
    (hFull0 : ∀ k, fullMismatch (3 * k) = t ^ k * u0)
    (hFull1 : ∀ k, fullMismatch (3 * k + 1) = t ^ k * u1)
    (hFull2 : ∀ k, fullMismatch (3 * k + 2) = t ^ k * u2) :
    (∀ m, 2 ≤ m →
      zeroMismatch m = zeroMismatchClosedForm CPlus CMinus lambdaPlus lambdaMinus m) ∧
      zeroMismatch 0 = z0 ∧
      zeroMismatch 1 = z1 ∧
      (∀ k r, r < 3 →
        fullMismatch (3 * k + r) = t ^ k * fullMismatchResidueValue u0 u1 u2 r) := by
  refine ⟨hZero, hZero0, hZero1, ?_⟩
  intro k r hr
  interval_cases r <;> simp [fullMismatchResidueValue, hFull0, hFull1, hFull2]

/-- Zero-mismatch specialization isolating the dominant `lambdaPlus` term and bounding the
    `lambdaMinus` remainder exactly.
    thm:fold-bernoulli-p-zero-mismatch-exact-tail -/
theorem paper_fold_bernoulli_p_zero_mismatch_exact_tail
    (zeroMismatch : ℕ → ℚ) (lambdaPlus lambdaMinus CPlus CMinus A : ℚ)
    (hZero : ∀ m,
      zeroMismatch m = zeroMismatchClosedForm CPlus CMinus lambdaPlus lambdaMinus m)
    (hTail : ∀ m, |CMinus * lambdaMinus ^ m| <= A * |lambdaMinus| ^ m) :
    (∀ m, zeroMismatch m = zeroMismatchClosedForm CPlus CMinus lambdaPlus lambdaMinus m) ∧
      (∀ m, |zeroMismatch m - CPlus * lambdaPlus ^ m| <= A * |lambdaMinus| ^ m) := by
  refine ⟨hZero, ?_⟩
  intro m
  have hrewrite : zeroMismatch m - CPlus * lambdaPlus ^ m = CMinus * lambdaMinus ^ m := by
    rw [hZero m, zeroMismatchClosedForm]
    ring
  rw [hrewrite]
  exact hTail m

end Omega.Folding
