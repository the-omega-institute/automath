import Omega.OperatorAlgebra.FkdetChiSectorFactorization
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete frozen-sector data for the four `χ`-sector variational problem. -/
structure conclusion_chi_variational_sector_maximization_data where
  conclusion_chi_variational_sector_maximization_weight :
    Omega.OperatorAlgebra.ChiSector → ℝ
  conclusion_chi_variational_sector_maximization_center_sector :
    Omega.OperatorAlgebra.ChiSector
  conclusion_chi_variational_sector_maximization_ratio_bound : ℝ
  conclusion_chi_variational_sector_maximization_frozen_concentration :
    ∀ σ, σ ≠ conclusion_chi_variational_sector_maximization_center_sector →
      conclusion_chi_variational_sector_maximization_weight σ ≤
        conclusion_chi_variational_sector_maximization_ratio_bound *
          conclusion_chi_variational_sector_maximization_weight
            conclusion_chi_variational_sector_maximization_center_sector
  conclusion_chi_variational_sector_maximization_max_fiber_homogeneity :
    ∀ σ, σ ≠ conclusion_chi_variational_sector_maximization_center_sector →
      conclusion_chi_variational_sector_maximization_weight σ <
      conclusion_chi_variational_sector_maximization_weight
          conclusion_chi_variational_sector_maximization_center_sector

namespace conclusion_chi_variational_sector_maximization_data

/-- The center sector is the unique maximizer of the four sector weights. -/
def conclusion_chi_variational_sector_maximization_unique_max_sector
    (D : conclusion_chi_variational_sector_maximization_data) : Prop :=
  ∃! σ, ∀ τ,
    D.conclusion_chi_variational_sector_maximization_weight τ ≤
      D.conclusion_chi_variational_sector_maximization_weight σ

/-- Every off-center sector satisfies the frozen-phase ratio bound. -/
def conclusion_chi_variational_sector_maximization_off_sector_ratio_bound
    (D : conclusion_chi_variational_sector_maximization_data) : Prop :=
  ∀ σ, σ ≠ D.conclusion_chi_variational_sector_maximization_center_sector →
    D.conclusion_chi_variational_sector_maximization_weight σ ≤
      D.conclusion_chi_variational_sector_maximization_ratio_bound *
        D.conclusion_chi_variational_sector_maximization_weight
          D.conclusion_chi_variational_sector_maximization_center_sector

end conclusion_chi_variational_sector_maximization_data

/-- Paper label: `thm:conclusion-chi-variational-sector-maximization`. -/
theorem paper_conclusion_chi_variational_sector_maximization
    (D : conclusion_chi_variational_sector_maximization_data) :
    D.conclusion_chi_variational_sector_maximization_unique_max_sector ∧
      D.conclusion_chi_variational_sector_maximization_off_sector_ratio_bound := by
  refine ⟨?_, D.conclusion_chi_variational_sector_maximization_frozen_concentration⟩
  refine ⟨D.conclusion_chi_variational_sector_maximization_center_sector, ?_, ?_⟩
  · intro τ
    by_cases hτ :
        τ = D.conclusion_chi_variational_sector_maximization_center_sector
    · simp [hτ]
    · exact le_of_lt
        (D.conclusion_chi_variational_sector_maximization_max_fiber_homogeneity τ hτ)
  · intro σ hσ
    by_contra hne
    have hcenter_le :
        D.conclusion_chi_variational_sector_maximization_weight
            D.conclusion_chi_variational_sector_maximization_center_sector ≤
          D.conclusion_chi_variational_sector_maximization_weight σ :=
      hσ D.conclusion_chi_variational_sector_maximization_center_sector
    have hσ_lt :
        D.conclusion_chi_variational_sector_maximization_weight σ <
          D.conclusion_chi_variational_sector_maximization_weight
            D.conclusion_chi_variational_sector_maximization_center_sector :=
      D.conclusion_chi_variational_sector_maximization_max_fiber_homogeneity σ hne
    linarith

end Omega.Conclusion
