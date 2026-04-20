import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.POM.KCollisionMittagLefflerScaling

namespace Omega.Zeta

open Omega.POM

/-- The dominant Jordan-block coefficient at collision order `k`, coefficient index `r`, and time
`n`. -/
noncomputable def xiJordanDominantBlockCoeff (k r n : ℕ) (u : ℝ) : ℝ :=
  pomKCollisionScaledCoeff k r n u

/-- The limiting Mittag-Leffler coefficient for the dominant Jordan block. -/
noncomputable def xiJordanUniversalKernelCoeff (k r : ℕ) (u : ℝ) : ℝ :=
  pomKCollisionMittagLefflerCoeff k r u

/-- A full family consisting of the dominant Jordan block plus an exponentially decaying
spectral-gap remainder. -/
noncomputable def xiJordanFullFamily (k r n : ℕ) (u C ρ : ℝ) : ℝ :=
  xiJordanDominantBlockCoeff k r n u + C * ρ ^ n

/-- Paper label: `thm:xi-mittag-leffler-universal-kfold-jordan-collision`.
The dominant `k`-fold Jordan block has the explicit binomial/factorial coefficient package already
formalized in `Omega.POM`, and adding an exponentially small spectral-gap term leaves the family
uniformly within `|C|` of the dominant block when `|ρ| ≤ 1`. -/
theorem paper_xi_mittag_leffler_universal_kfold_jordan_collision
    (k r n : ℕ) (u C ρ : ℝ) (hρ : |ρ| ≤ 1) :
    xiJordanDominantBlockCoeff k r n u =
      ((Nat.choose (n + pomKCollisionMittagLefflerOrder k r)
          (pomKCollisionMittagLefflerOrder k r) : ℝ) * (-u) ^ r) /
        (n + 1 : ℝ) ^ pomKCollisionMittagLefflerOrder k r ∧
      xiJordanUniversalKernelCoeff k r u =
        (-u) ^ r / (Nat.factorial (pomKCollisionMittagLefflerOrder k r) : ℝ) ∧
      ((Nat.choose (n + pomKCollisionMittagLefflerOrder k r)
          (pomKCollisionMittagLefflerOrder k r) : ℝ) ≤
        ((n + pomKCollisionMittagLefflerOrder k r : ℕ) : ℝ) ^
            pomKCollisionMittagLefflerOrder k r /
          (Nat.factorial (pomKCollisionMittagLefflerOrder k r) : ℝ)) ∧
      |xiJordanFullFamily k r n u C ρ - xiJordanDominantBlockCoeff k r n u| = |C| * |ρ| ^ n ∧
      |xiJordanFullFamily k r n u C ρ - xiJordanDominantBlockCoeff k r n u| ≤ |C| := by
  rcases paper_pom_kcollision_mittag_leffler_scaling k r n u with ⟨hdom, hml, hchoose⟩
  have htail :
      |xiJordanFullFamily k r n u C ρ - xiJordanDominantBlockCoeff k r n u| = |C| * |ρ| ^ n := by
    unfold xiJordanFullFamily xiJordanDominantBlockCoeff
    rw [add_sub_cancel_left, abs_mul, abs_pow]
  have hpow : |ρ| ^ n ≤ 1 := pow_le_one₀ (abs_nonneg ρ) hρ
  have hbound :
      |xiJordanFullFamily k r n u C ρ - xiJordanDominantBlockCoeff k r n u| ≤ |C| := by
    rw [htail]
    calc
      |C| * |ρ| ^ n ≤ |C| * 1 := by gcongr
      _ = |C| := by simp
  exact ⟨hdom, hml, hchoose, htail, hbound⟩

end Omega.Zeta
