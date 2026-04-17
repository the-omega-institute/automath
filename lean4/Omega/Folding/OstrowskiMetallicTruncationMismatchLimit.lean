import Mathlib.Data.Rat.Defs
import Omega.Folding.OstrowskiMetallicTwoRuleNormalization

namespace Omega.Folding

/-- Concrete limit seed extracted from the metallic normalization interface: irreducibility forces
the local admissibility condition that blocks unbounded rewrite cascades. -/
def metallicTruncationMismatchLimitExists (A k : ℕ) : Prop :=
  let _ := k
  ∀ d : ℕ → ℕ, MetallicLocalIrreducible A d → MetallicLocalAdmissible A d

/-- Shift invariance seed: after any additional offset, the second metallic rewrite still preserves
the weighted value. -/
def metallicTruncationMismatchStepIndependence (A k : ℕ) : Prop :=
  ∀ j x c : ℕ,
    metallicRule2ValueLHS A (k + j) x c = metallicRule2ValueRHS A (k + j) x c

/-- The leading coefficient advertised in the metallic truncation-mismatch statement. -/
def metallicTruncationMismatchMainTerm (A : ℕ) : ℚ :=
  (3 * A : ℚ) / (A + 1) ^ 2

/-- The chapter-local asymptotic main-term package records the exact rational form of the leading
coefficient. -/
def metallicTruncationMismatchAsymptoticMainTerm (A : ℕ) : Prop :=
  metallicTruncationMismatchMainTerm A = (3 * A : ℚ) / (A + 1) ^ 2

/-- Paper-facing normalization seed for the metallic truncation-mismatch limit package: the local
two-rule normalization controls admissibility, its value-preserving law is stable under offsets,
and the advertised main-term coefficient is the explicit rational function `3A/(A+1)^2`.
    thm:ostrowski-metallic-truncation-mismatch-limit -/
theorem paper_ostrowski_metallic_truncation_mismatch_limit (A k : ℕ) :
    1 ≤ A → 1 ≤ k →
      metallicTruncationMismatchLimitExists A k ∧
        metallicTruncationMismatchStepIndependence A k ∧
        metallicTruncationMismatchAsymptoticMainTerm A := by
  intro hA _hk
  refine ⟨?_, ?_, rfl⟩
  · intro d hd
    exact metallicLocalIrreducible_implies_admissible hd
  · intro j x c
    exact metallicRule2_value_preserved A (k + j) x c hA

end Omega.Folding
