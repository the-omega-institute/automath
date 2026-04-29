import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.NumberTheory.Real.GoldenRatio
import Omega.Folding.FoldCondexpIndexMaxFiber
import Omega.Zeta.DephysFoldStinespringSqrtLaw

namespace Omega.Zeta

/-- The hidden-label capacity is the fold conditional-expectation index, identified here with the
maximal fold-fiber multiplicity. -/
noncomputable def dephys_fold_hidden_label_cap_sqrt_hidden_label_cap (m : ℕ) : ℕ :=
  Omega.X.maxFiberMultiplicity m

/-- Stinespring square bound rewritten in terms of the hidden-label capacity. -/
noncomputable def dephys_fold_hidden_label_cap_sqrt_stinespring_bound (m d : ℕ) : Prop :=
  (dephys_fold_hidden_label_cap_sqrt_hidden_label_cap m : ℝ) ≤ (d : ℝ) ^ 2

/-- Paper label: `cor:dephys-fold-hidden-label-cap-sqrt`. -/
theorem paper_dephys_fold_hidden_label_cap_sqrt
    (k d : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 5)
    (hStine : dephys_fold_hidden_label_cap_sqrt_stinespring_bound (2 * k) d) :
    dephys_fold_hidden_label_cap_sqrt_hidden_label_cap (2 * k) =
      Omega.X.maxFiberMultiplicity (2 * k) ∧
      (∃ x : Omega.X (2 * k),
        Omega.X.fiberMultiplicity x =
          dephys_fold_hidden_label_cap_sqrt_hidden_label_cap (2 * k)) ∧
      (∀ x : Omega.X (2 * k),
        Omega.X.fiberMultiplicity x ≤
          dephys_fold_hidden_label_cap_sqrt_hidden_label_cap (2 * k)) ∧
      0 < dephys_fold_hidden_label_cap_sqrt_hidden_label_cap (2 * k) ∧
      dephys_fold_hidden_label_cap_sqrt_hidden_label_cap (2 * k) = Nat.fib (k + 2) ∧
      Real.sqrt (dephys_fold_hidden_label_cap_sqrt_hidden_label_cap (2 * k)) ≤ d ∧
      Real.sqrt (Real.goldenRatio ^ k / 2) ≤ d := by
  have hindex := Omega.paper_fold_condexp_index_maxfiber (2 * k)
  have hsqrt :=
    paper_dephys_fold_stinespring_sqrt_law k d hk hk'
      (by simpa [dephys_fold_hidden_label_cap_sqrt_stinespring_bound,
        dephys_fold_hidden_label_cap_sqrt_hidden_label_cap] using hStine)
  have hclosed :
      dephys_fold_hidden_label_cap_sqrt_hidden_label_cap (2 * k) = Nat.fib (k + 2) := by
    simpa [dephys_fold_hidden_label_cap_sqrt_hidden_label_cap] using
      Omega.X.maxFiberMultiplicity_even_ext k hk hk'
  refine ⟨rfl, ?_, ?_, ?_, hclosed, ?_, ?_⟩
  · simpa [dephys_fold_hidden_label_cap_sqrt_hidden_label_cap] using hindex.1
  · simpa [dephys_fold_hidden_label_cap_sqrt_hidden_label_cap] using hindex.2.1
  · simpa [dephys_fold_hidden_label_cap_sqrt_hidden_label_cap] using hindex.2.2.1
  · simpa [dephys_fold_hidden_label_cap_sqrt_hidden_label_cap] using hsqrt.2.2.1
  · exact hsqrt.2.2.2

end Omega.Zeta
