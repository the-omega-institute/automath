import Omega.CircleDimension.ResidualCircleDim

namespace Omega.CircleDimension.ResidualCircleDimLaws

/-- Paper-facing seed package for residual circle-dimension laws.
    prop:cdim-residual-circle-dimension-laws -/
theorem paper_cdim_residual_circle_dim_laws_seeds :
    (∀ R S : ℕ → ℕ, ∀ b : ℕ, R b ≤ S b →
      Omega.CircleDimension.residualCdimAt R b ≤ Omega.CircleDimension.residualCdimAt S b) ∧
    (∀ a b : ℕ, 2 ^ a * 2 ^ b = 2 ^ (a + b)) ∧
    (∀ a b : ℕ, Nat.log 2 (2 ^ a * 2 ^ b) = Nat.log 2 (2 ^ a) + Nat.log 2 (2 ^ b)) := by
  refine ⟨Omega.CircleDimension.residualCdimAt_mono_of_card_le, ?_, ?_⟩
  · intro a b
    exact Omega.CircleDimension.residual_register_pow_add a b
  · intro a b
    rw [← pow_add, Nat.log_pow (by norm_num : 1 < 2),
      Nat.log_pow (by norm_num : 1 < 2), Nat.log_pow (by norm_num : 1 < 2)]

/-- Wrapper theorem matching the paper-facing package name. -/
theorem paper_cdim_residual_circle_dim_laws_package :
    (∀ R S : ℕ → ℕ, ∀ b : ℕ, R b ≤ S b →
      Omega.CircleDimension.residualCdimAt R b ≤ Omega.CircleDimension.residualCdimAt S b) ∧
    (∀ a b : ℕ, 2 ^ a * 2 ^ b = 2 ^ (a + b)) ∧
    (∀ a b : ℕ, Nat.log 2 (2 ^ a * 2 ^ b) = Nat.log 2 (2 ^ a) + Nat.log 2 (2 ^ b)) :=
  paper_cdim_residual_circle_dim_laws_seeds

/-- Paper label: `prop:cdim-residual-circle-dimension-laws`. -/
theorem paper_cdim_residual_circle_dimension_laws :
    (∀ R S : ℕ → ℕ, ∀ b : ℕ, R b ≤ S b →
      Omega.CircleDimension.residualCdimAt R b ≤ Omega.CircleDimension.residualCdimAt S b) ∧
    (∀ a b : ℕ, 2 ^ a * 2 ^ b = 2 ^ (a + b)) ∧
    (∀ a b : ℕ, Nat.log 2 (2 ^ a * 2 ^ b) = Nat.log 2 (2 ^ a) + Nat.log 2 (2 ^ b)) :=
  paper_cdim_residual_circle_dim_laws_package

end Omega.CircleDimension.ResidualCircleDimLaws
