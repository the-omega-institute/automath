import Omega.Conclusion.CofinalPrimeSupportNoUniformBoundedRankLedger
import Omega.Conclusion.FixedResolutionCollisionRationalHankelRank
import Omega.Conclusion.FixedresolutionTopdownPeeling
import Omega.POM.FiberSpectrumFiniteReconstructionSharp

namespace Omega.Conclusion

open scoped BigOperators

/-- Paper-facing finite-spectrum closure package at fixed resolution: rational Hankel rank,
first-`2s` reconstruction sufficiency, top-down Prony peeling, and no uniform fixed-rank ledger. -/
def conclusion_fixedresolution_collision_axis_finitespectrum_closure_statement : Prop :=
  (∀ (r N : ℕ) (δ μ : Fin r → ℚ) (z : ℚ), StrictMono δ → (∀ i, μ i ≠ 0) →
    (∀ i, δ i * z ≠ 1) →
      (fixedResolutionCollisionGeneratingPrefix δ μ z N =
        fixedResolutionCollisionPartialFraction δ μ z N) ∧
      (∀ i j, fixedResolutionCollisionHankelEntry δ μ i j =
        fixedResolutionCollisionGramEntry δ μ i j) ∧
      fixedResolutionCollisionDeterminantWitness δ μ ∧
      fixedResolutionCollisionExactHankelRank r) ∧
    (∀ (D : Omega.POM.FiberSpectrumPronyHankelRankData), 2 ≤ D.atomCount →
      Omega.POM.pom_fiber_spectrum_finite_reconstruction_sharp_window D.atomCount =
          2 * D.atomCount ∧
        Omega.POM.pom_fiber_spectrum_finite_reconstruction_sharp_reconstructs D ∧
        (∀ k : ℕ,
          k ≤ Omega.POM.pom_fiber_spectrum_finite_reconstruction_sharp_window D.atomCount - 2 →
            Omega.POM.pomPronyHankelThresholdGap D.atomCount k = 0) ∧
        Omega.POM.pomPronyHankelThresholdGap D.atomCount
            (Omega.POM.pom_fiber_spectrum_finite_reconstruction_sharp_window D.atomCount - 1) =
          Nat.factorial
            (Omega.POM.pom_fiber_spectrum_finite_reconstruction_sharp_window D.atomCount - 1)) ∧
    (∀ (s : ℕ) (δ μ : ℕ → ℝ), ∀ r ≤ s, ∀ q : ℕ,
      conclusion_fixedresolution_topdown_peeling_residual s δ μ r q =
        ∑ j ∈ Finset.Icc 1 (s - r), μ j * δ j ^ q) ∧
    (∀ R : ℕ,
      ∃ n : ℕ,
        R < n ∧
          ¬ ∃ Φ :
              conclusion_cofinal_prime_support_no_uniform_bounded_rank_ledger_source n →ₗ[ℚ]
                conclusion_cofinal_prime_support_no_uniform_bounded_rank_ledger_target R,
            Function.Injective Φ)

/-- Paper label: `thm:conclusion-fixedresolution-collision-axis-finitespectrum-closure`. -/
theorem paper_conclusion_fixedresolution_collision_axis_finitespectrum_closure :
    conclusion_fixedresolution_collision_axis_finitespectrum_closure_statement := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r N δ μ z hδ hμ hz
    exact paper_conclusion_fixedresolution_collision_rational_hankel_rank r N δ μ z hδ hμ hz
  · intro D hD
    exact Omega.POM.paper_pom_fiber_spectrum_finite_reconstruction_sharp D hD
  · intro s δ μ
    exact paper_conclusion_fixedresolution_topdown_peeling s δ μ
  · intro R
    exact paper_conclusion_cofinal_prime_support_no_uniform_bounded_rank_ledger R

end Omega.Conclusion
