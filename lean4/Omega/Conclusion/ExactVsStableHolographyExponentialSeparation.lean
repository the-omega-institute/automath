import Mathlib.Tactic
import Omega.Conclusion.BoundaryStokesStrictLinearHolography
import Omega.SPG.DyadicHolographicReconstructionNoiseBudget

namespace Omega.Conclusion

/-- Bundled fixed-resolution conclusion: exact boundary Stokes reconstruction is available, while
the dyadic noise budget is forced onto the exponentially shrinking threshold
`sqrt (2n) * delta * 2^(-m/2)`. -/
def conclusion_exact_vs_stable_holography_exponential_separation_statement : Prop :=
  ∀ (m n : ℕ) (_hn : 0 < n) (epsilon delta : ℝ),
    Function.Bijective (boundaryStokesStrictLinearHolography m n) ∧
      ((((1 / Real.sqrt (2 * n : ℝ)) * (2 : ℝ) ^ (m / 2 : ℝ)) * epsilon ≤ delta) ↔
        epsilon ≤ Real.sqrt (2 * n : ℝ) * delta * (2 : ℝ) ^ (-(m / 2 : ℝ)))

/-- Paper label: `thm:conclusion-exact-vs-stable-holography-exponential-separation`. -/
theorem paper_conclusion_exact_vs_stable_holography_exponential_separation :
    conclusion_exact_vs_stable_holography_exponential_separation_statement := by
  intro m n hn epsilon delta
  exact ⟨(paper_conclusion_boundary_stokes_strict_linear_holography m n).2,
    Omega.SPG.paper_spg_dyadic_holographic_reconstruction_noise_budget
      (n := n) (m := m) (ε := epsilon) (δ := delta) hn⟩

end Omega.Conclusion
