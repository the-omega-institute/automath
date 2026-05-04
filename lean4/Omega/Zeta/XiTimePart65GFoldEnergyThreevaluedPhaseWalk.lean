import Omega.Folding.FoldSpectrumFactorization

open scoped BigOperators

namespace Omega.Zeta

/--
Squaring the normalized fold-spectrum modulus turns the product of absolute cosine factors into
the product of squared cosine factors.

thm:xi-time-part65g-fold-energy-threevalued-phase-walk
-/
theorem paper_xi_time_part65g_fold_energy_threevalued_phase_walk {m : ℕ}
    (w : Fin m → ℝ) (θ : ℝ) :
    ‖Omega.Folding.normalizedResidueProfileFourier w θ‖ ^ 2 =
      ∏ j : Fin m, (Real.cos (w j * θ)) ^ 2 := by
  have hnorm :
      ‖Omega.Folding.normalizedResidueProfileFourier w θ‖ =
        ∏ j : Fin m, |Real.cos (w j * θ)| :=
    (Omega.Folding.paper_fold_spectrum_factorization w θ).2.2
  rw [hnorm, ← Finset.prod_pow]
  refine Finset.prod_congr rfl ?_
  intro j _
  exact sq_abs (Real.cos (w j * θ))

end Omega.Zeta
