import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Omega.Conclusion.LkNormalizedZetaOddProjector

namespace Omega.Conclusion

noncomputable section

/-- The residue contribution from the change of variables `u = 2s`. -/
def conclusion_lk_normalized_zeta_residue_quarter_uResidue : ℝ :=
  1 / 2

/-- The limiting odd-projector residue at `s = 1/2`. -/
def conclusion_lk_normalized_zeta_residue_quarter_limitResidue : ℝ :=
  (1 - (2 : ℝ) ^ (-2 * (1 / 2 : ℝ))) * conclusion_lk_normalized_zeta_residue_quarter_uResidue

/-- Concrete statement for the residue-quarter corollary. -/
def conclusion_lk_normalized_zeta_residue_quarter_statement : Prop :=
  (∀ k : ℕ,
      conclusion_lk_normalized_zeta_odd_projector_odd_projector k (1 / 2) =
        (1 / 2 : ℝ) * Omega.POM.pom_lk_spectral_zeta_dirichlet_full_sum k (1 / 2)) ∧
    conclusion_lk_normalized_zeta_residue_quarter_limitResidue = (1 / 4 : ℝ)

/-- Paper label: `cor:conclusion-Lk-normalized-zeta-residue-quarter`. Evaluating the odd-projector
factor at `s = 1/2` gives `1/2`, the variable change `u = 2s` contributes another `1/2`, and the
product is the residue `1/4`. -/
theorem paper_conclusion_lk_normalized_zeta_residue_quarter :
    conclusion_lk_normalized_zeta_residue_quarter_statement := by
  refine ⟨?_, ?_⟩
  · intro k
    have hodd := (paper_conclusion_lk_normalized_zeta_odd_projector).2.1 k (1 / 2 : ℝ)
    have hpow :
        (2 : ℝ) ^ (-2 * (1 / 2 : ℝ)) = (1 / 2 : ℝ) := by
      rw [show (-2 : ℝ) * (1 / 2 : ℝ) = (-1 : ℝ) by ring]
      rw [Real.rpow_neg_one]
      norm_num
    rw [hpow] at hodd
    norm_num at hodd ⊢
    simpa [mul_comm] using hodd
  · unfold conclusion_lk_normalized_zeta_residue_quarter_limitResidue
    unfold conclusion_lk_normalized_zeta_residue_quarter_uResidue
    rw [show (-2 : ℝ) * (1 / 2 : ℝ) = (-1 : ℝ) by ring, Real.rpow_neg_one]
    norm_num

end

end Omega.Conclusion
