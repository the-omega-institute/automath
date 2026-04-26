import Omega.POM.PhiLogisticPosteriorGrid

open scoped BigOperators

namespace Omega.POM

/-- Paper label: `cor:pom-phi-logit-lattice-translation`. -/
theorem paper_pom_phi_logit_lattice_translation (B : ℕ → Bool) :
    let Z : ℕ → ℤ :=
      fun n => Finset.sum (Finset.range n) fun i => if B i then (1 : ℤ) else -1;
    (∀ n, Real.goldenRatio ^ (Z n) =
        Finset.prod (Finset.range n) fun i =>
          if B i then Real.goldenRatio else Real.goldenRatio⁻¹) ∧
      (∀ n, Z (n + 1) = Z n + (if B n then (1 : ℤ) else -1)) := by
  dsimp
  constructor
  · intro n
    induction n with
    | zero =>
        simp
    | succ n ih =>
        rw [Finset.sum_range_succ, Finset.prod_range_succ]
        by_cases hB : B n
        · simp [hB, ih, zpow_add₀ Real.goldenRatio_ne_zero]
        · simp [hB, ih, zpow_add₀ Real.goldenRatio_ne_zero]
  · intro n
    rw [Finset.sum_range_succ]

end Omega.POM
