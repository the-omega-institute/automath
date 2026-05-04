import Mathlib.Tactic
import Omega.POM.ConclusionPomSizeBiasMonotonicity
import Omega.POM.TowerDefectPinskerBound

namespace Omega.POM

/-- Concrete data for the third-obstruction curvature envelope.  The observable `psi` is the
already-specialized logarithmic fiber potential on the middle tower, while `oscillation`, `tv`,
and `pinskerScale` record the total-variation envelope used by the existing tower Pinsker bound. -/
structure conclusion_pom_third_obstruction_curvature_envelope_data where
  X : Type*
  Y : Type*
  Z : Type*
  W : Type*
  instFintypeX : Fintype X
  instFintypeY : Fintype Y
  instFintypeZ : Fintype Z
  instFintypeW : Fintype W
  instDecidableEqX : DecidableEq X
  instDecidableEqY : DecidableEq Y
  instDecidableEqZ : DecidableEq Z
  instDecidableEqW : DecidableEq W
  f : X → Y
  g : Y → Z
  h : Z → W
  psi : Y → ℚ
  hf : Function.Surjective f
  hg : Function.Surjective g
  w : W
  hw : 0 < towerFiberCard h w
  oscillation : ℚ
  tv : ℚ
  pinskerScale : ℚ
  oscillation_nonneg : 0 ≤ oscillation
  oscillation_tv_bound :
    |pom_tower_defect_pinsker_bound_uniformExpectation g h psi w -
        pom_tower_defect_pinsker_bound_sizeBiasedExpectation g h psi w| ≤
      oscillation * tv
  tv_pinsker_bound : tv ≤ pinskerScale

attribute [instance] conclusion_pom_third_obstruction_curvature_envelope_data.instFintypeX
attribute [instance] conclusion_pom_third_obstruction_curvature_envelope_data.instFintypeY
attribute [instance] conclusion_pom_third_obstruction_curvature_envelope_data.instFintypeZ
attribute [instance] conclusion_pom_third_obstruction_curvature_envelope_data.instFintypeW
attribute [instance] conclusion_pom_third_obstruction_curvature_envelope_data.instDecidableEqX
attribute [instance] conclusion_pom_third_obstruction_curvature_envelope_data.instDecidableEqY
attribute [instance] conclusion_pom_third_obstruction_curvature_envelope_data.instDecidableEqZ
attribute [instance] conclusion_pom_third_obstruction_curvature_envelope_data.instDecidableEqW

/-- The envelope conclusion: the third obstruction is the tower-defect gap, it satisfies the
oscillation-TV and Pinsker bounds, and its sign is controlled by the covariance sign. -/
def conclusion_pom_third_obstruction_curvature_envelope_holds
    (D : conclusion_pom_third_obstruction_curvature_envelope_data) : Prop :=
  pom_tower_defect_pinsker_bound_towerDefect D.g D.h D.psi D.w =
      pom_tower_defect_pinsker_bound_uniformExpectation D.g D.h D.psi D.w -
        pom_tower_defect_pinsker_bound_sizeBiasedExpectation D.g D.h D.psi D.w ∧
    pom_tower_defect_pinsker_bound_towerDefect D.g D.h D.psi D.w =
      -towerDefectCovariance D.g D.h D.psi D.w /
        towerFiberAverage D.h (fun z => (towerFiberCard D.g z : ℚ)) D.w ∧
    |pom_tower_defect_pinsker_bound_towerDefect D.g D.h D.psi D.w| ≤
      D.oscillation * D.tv ∧
    |pom_tower_defect_pinsker_bound_towerDefect D.g D.h D.psi D.w| ≤
      D.oscillation * D.pinskerScale ∧
    (0 ≤ towerDefectCovariance D.g D.h D.psi D.w →
      pom_tower_defect_pinsker_bound_towerDefect D.g D.h D.psi D.w ≤ 0) ∧
    (towerDefectCovariance D.g D.h D.psi D.w ≤ 0 →
      0 ≤ pom_tower_defect_pinsker_bound_towerDefect D.g D.h D.psi D.w) ∧
    (0 < towerDefectCovariance D.g D.h D.psi D.w →
      pom_tower_defect_pinsker_bound_towerDefect D.g D.h D.psi D.w < 0) ∧
    (towerDefectCovariance D.g D.h D.psi D.w < 0 →
      0 < pom_tower_defect_pinsker_bound_towerDefect D.g D.h D.psi D.w)

private lemma conclusion_pom_third_obstruction_curvature_envelope_mean_pos
    (D : conclusion_pom_third_obstruction_curvature_envelope_data) :
    0 < towerFiberAverage D.h (fun z => (towerFiberCard D.g z : ℚ)) D.w := by
  have hsum_nat : 0 < Finset.sum (towerFiber D.h D.w) (fun z => towerFiberCard D.g z) := by
    rcases Finset.card_pos.mp D.hw with ⟨z, hz⟩
    have hzpos : 0 < towerFiberCard D.g z := towerFiberCard_pos_of_surjective D.g D.hg z
    have hle :
        towerFiberCard D.g z ≤
          Finset.sum (towerFiber D.h D.w) (fun z' => towerFiberCard D.g z') := by
      exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hz
    exact lt_of_lt_of_le hzpos hle
  have hsum : 0 < Finset.sum (towerFiber D.h D.w) (fun z => (towerFiberCard D.g z : ℚ)) := by
    exact_mod_cast hsum_nat
  have hcard : 0 < (towerFiberCard D.h D.w : ℚ) := by
    exact_mod_cast D.hw
  simpa [towerFiberAverage] using div_pos hsum hcard

/-- Paper label: `thm:conclusion-pom-third-obstruction-curvature-envelope`. -/
theorem paper_conclusion_pom_third_obstruction_curvature_envelope
    (D : conclusion_pom_third_obstruction_curvature_envelope_data) :
    conclusion_pom_third_obstruction_curvature_envelope_holds D := by
  have hPinsker :=
    paper_pom_tower_defect_pinsker_bound D.g D.h D.psi D.hg D.w D.hw
      D.oscillation D.tv D.pinskerScale D.oscillation_tv_bound D.tv_pinsker_bound
      D.oscillation_nonneg
  rcases hPinsker with ⟨hDef, hCov, hTv, hScale⟩
  have hMean : 0 < towerFiberAverage D.h (fun z => (towerFiberCard D.g z : ℚ)) D.w :=
    conclusion_pom_third_obstruction_curvature_envelope_mean_pos D
  have hNondec :
      0 ≤ towerDefectCovariance D.g D.h D.psi D.w →
        pom_tower_defect_pinsker_bound_towerDefect D.g D.h D.psi D.w ≤ 0 := by
    intro hcov_nonneg
    rw [hCov]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt hMean)
  have hNoninc :
      towerDefectCovariance D.g D.h D.psi D.w ≤ 0 →
        0 ≤ pom_tower_defect_pinsker_bound_towerDefect D.g D.h D.psi D.w := by
    intro hcov_nonpos
    rw [hCov]
    exact div_nonneg (by linarith) (le_of_lt hMean)
  have hStrictNondec :
      0 < towerDefectCovariance D.g D.h D.psi D.w →
        pom_tower_defect_pinsker_bound_towerDefect D.g D.h D.psi D.w < 0 := by
    intro hcov_pos
    rw [hCov]
    exact div_neg_of_neg_of_pos (by linarith) hMean
  have hStrictNoninc :
      towerDefectCovariance D.g D.h D.psi D.w < 0 →
        0 < pom_tower_defect_pinsker_bound_towerDefect D.g D.h D.psi D.w := by
    intro hcov_neg
    rw [hCov]
    exact div_pos (by linarith) hMean
  exact ⟨hDef, hCov, hTv, hScale, hNondec, hNoninc, hStrictNondec, hStrictNoninc⟩

end Omega.POM
