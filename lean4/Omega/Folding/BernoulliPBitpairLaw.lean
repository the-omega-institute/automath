import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Bernoulli-p bitpair law

Closed-form identities for the stationary joint law and mismatch density.
-/

namespace Omega.Folding

/-- Closed form of the stationary Bernoulli-`p` input/output bitpair law.
    prop:fold-gauge-anomaly-bernoulli-p-bitpair-law -/
theorem paper_fold_gauge_anomaly_bernoulli_p_bitpair_law
    (p : Real) (_hp0 : 0 <= p) (_hp1 : p <= 1) :
    let q00 := (1 - p - p^2 + 2 * p^3 - p^4) / (1 + p^3)
    let q01 := (p^2 * (1 - p)) / (1 + p^3)
    let q10 := (p^2 * (2 - p)) / (1 + p^3)
    let q11 := (p * (p^3 + (1 - p)^2)) / (1 + p^3)
    q00 + q01 + q10 + q11 = 1 ∧
      p - (q01 + q11) = p^2 / (1 + p^3) ∧
      q01 + q10 = p^2 * (3 - 2 * p) / (1 + p^3) := by
  dsimp
  have hden : (1 + p ^ 3 : Real) ≠ 0 := by positivity
  refine ⟨?_, ?_, ?_⟩
  · field_simp [hden]
    ring_nf
  · field_simp [hden]
    ring_nf
  · field_simp [hden]
    ring_nf

end Omega.Folding
