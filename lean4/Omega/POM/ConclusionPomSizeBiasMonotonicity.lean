import Mathlib.Tactic
import Omega.POM.TowerDefectCovarianceLaw

namespace Omega.POM

/-- Concrete tower data for the size-bias monotonicity conclusion. The sign input is expressed as
the covariance sign on the `h`-fiber, so the tower-defect covariance law can be applied directly.
-/
structure conclusion_pom_size_bias_monotonicity_data where
  X : Type*
  Y : Type*
  Z : Type*
  instFintypeX : Fintype X
  instFintypeY : Fintype Y
  instFintypeZ : Fintype Z
  instDecidableEqX : DecidableEq X
  instDecidableEqY : DecidableEq Y
  instDecidableEqZ : DecidableEq Z
  g : X → Y
  h : Y → Z
  ψ : X → ℚ
  hg : Function.Surjective g
  z : Z
  hz : 0 < towerFiberCard h z
  covariance_nonpos : towerDefectCovariance g h ψ z ≤ 0

attribute [instance] conclusion_pom_size_bias_monotonicity_data.instFintypeX
attribute [instance] conclusion_pom_size_bias_monotonicity_data.instFintypeY
attribute [instance] conclusion_pom_size_bias_monotonicity_data.instFintypeZ
attribute [instance] conclusion_pom_size_bias_monotonicity_data.instDecidableEqX
attribute [instance] conclusion_pom_size_bias_monotonicity_data.instDecidableEqY
attribute [instance] conclusion_pom_size_bias_monotonicity_data.instDecidableEqZ

namespace conclusion_pom_size_bias_monotonicity_data

/-- The tower defect is the normalized negative covariance, so a nonpositive covariance forces the
uniform outer expectation to dominate the size-biased one. -/
def holds (D : conclusion_pom_size_bias_monotonicity_data) : Prop :=
  towerFiberAverage D.h (towerInnerAverage D.g D.ψ) D.z - towerCompositeAverage D.g D.h D.ψ D.z =
      -towerDefectCovariance D.g D.h D.ψ D.z /
        towerFiberAverage D.h (fun y => (towerFiberCard D.g y : ℚ)) D.z ∧
    towerCompositeAverage D.g D.h D.ψ D.z ≤
      towerFiberAverage D.h (towerInnerAverage D.g D.ψ) D.z

end conclusion_pom_size_bias_monotonicity_data

open conclusion_pom_size_bias_monotonicity_data

private lemma conclusion_pom_size_bias_monotonicity_mean_pos
    (D : conclusion_pom_size_bias_monotonicity_data) :
    0 < towerFiberAverage D.h (fun y => (towerFiberCard D.g y : ℚ)) D.z := by
  have hsum_nat : 0 < Finset.sum (towerFiber D.h D.z) (fun y => towerFiberCard D.g y) := by
    rcases Finset.card_pos.mp D.hz with ⟨y, hy⟩
    have hypos : 0 < towerFiberCard D.g y := towerFiberCard_pos_of_surjective D.g D.hg y
    have hle :
        towerFiberCard D.g y ≤
          Finset.sum (towerFiber D.h D.z) (fun y' => towerFiberCard D.g y') := by
      exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hy
    exact lt_of_lt_of_le hypos hle
  have hsum : 0 < Finset.sum (towerFiber D.h D.z) (fun y => (towerFiberCard D.g y : ℚ)) := by
    exact_mod_cast hsum_nat
  have hcard : 0 < (towerFiberCard D.h D.z : ℚ) := by
    exact_mod_cast D.hz
  simpa [towerFiberAverage] using div_pos hsum hcard

/-- Paper label: `thm:conclusion-pom-size-bias-monotonicity`. Once the tower defect is rewritten
by the covariance law, a nonpositive covariance makes the size-biased outer average no larger than
the uniform outer average. -/
theorem paper_conclusion_pom_size_bias_monotonicity
    (D : conclusion_pom_size_bias_monotonicity_data) : D.holds := by
  have hcov :=
    paper_pom_tower_defect_covariance_law D.g D.h D.ψ D.hg D.z D.hz
  have hmean_pos : 0 < towerFiberAverage D.h (fun y => (towerFiberCard D.g y : ℚ)) D.z :=
    conclusion_pom_size_bias_monotonicity_mean_pos D
  have hgap_nonneg :
      0 ≤ towerFiberAverage D.h (towerInnerAverage D.g D.ψ) D.z -
        towerCompositeAverage D.g D.h D.ψ D.z := by
    rw [hcov]
    have hnum_nonneg : 0 ≤ -towerDefectCovariance D.g D.h D.ψ D.z := by
      linarith [D.covariance_nonpos]
    exact div_nonneg hnum_nonneg (le_of_lt hmean_pos)
  have horder :
      towerCompositeAverage D.g D.h D.ψ D.z ≤
        towerFiberAverage D.h (towerInnerAverage D.g D.ψ) D.z := by
    linarith
  exact ⟨hcov, horder⟩

end Omega.POM
