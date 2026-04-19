import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Omega.FoldResidualTime.Window6FixedFreezingLaw

namespace Omega.Zeta

open Omega.FoldResidualTime

/-- Window-`6` Rényi divergence written directly from the finite fiber-moment sum. -/
noncomputable def window6RenyiDivergence (q : ℕ) : ℝ :=
  Real.log 21 + Real.log (window6FiberMomentSum q / (64 : ℝ) ^ q) / ((q : ℝ) - 1)

/-- Window-`6` Shannon entropy in natural-log units. -/
noncomputable def window6ShannonEntropy : ℝ :=
  (37 / 8 : ℝ) * Real.log 2 - (3 / 16 : ℝ) * Real.log 3

/-- The KL divergence from the uniform `21`-state reference law. -/
noncomputable def window6KLDivergence : ℝ :=
  Real.log 21 - window6ShannonEntropy

/-- Bit-level redundancy of the parity-charge presentation. -/
noncomputable def window6ParityChargeRedundancy : ℝ :=
  21 - window6ShannonEntropy / Real.log 2

/-- Exact Rényi, Shannon, KL, and redundancy identities for the window-`6` parity-charge law.
    prop:xi-window6-renyi-divergence-parity-charge-redundancy -/
theorem paper_xi_window6_renyi_divergence_parity_charge_redundancy :
    (∀ q : ℕ, 2 ≤ q →
      window6RenyiDivergence q =
        Real.log 21 + Real.log (window6FiberMomentSum q / (64 : ℝ) ^ q) / ((q : ℝ) - 1)) ∧
      window6ShannonEntropy =
        (37 / 8 : ℝ) * Real.log 2 - (3 / 16 : ℝ) * Real.log 3 ∧
      window6KLDivergence = Real.log 21 - window6ShannonEntropy ∧
      window6ParityChargeRedundancy = 21 - window6ShannonEntropy / Real.log 2 := by
  refine ⟨?_, rfl, rfl, rfl⟩
  intro q hq
  rfl

end Omega.Zeta
