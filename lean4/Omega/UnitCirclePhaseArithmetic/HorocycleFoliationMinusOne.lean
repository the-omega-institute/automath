import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic

namespace Omega.UnitCirclePhaseArithmetic

private lemma normSq_add_one (w : ℂ) :
    Complex.normSq (1 + w) = Complex.normSq w + 1 + 2 * Complex.re w := by
  simp [Complex.normSq_apply]
  ring

private lemma normSq_add_real (w : ℂ) (a : ℝ) :
    Complex.normSq (w + a) = Complex.normSq w + a ^ 2 + 2 * a * Complex.re w := by
  simp [Complex.normSq_apply]
  ring

theorem paper_app_horocycle_foliation_minus1 {δ : ℝ} (hδ : 0 < δ) :
    {w : ℂ | Complex.normSq w < 1 ∧ (1 - Complex.normSq w) / Complex.normSq (1 + w) = δ} =
      {w : ℂ |
        Complex.normSq w < 1 ∧
          Complex.normSq (w + (δ / (1 + δ) : ℝ)) = (1 / (1 + δ)) ^ 2} := by
  ext w
  have hδ1_ne : 1 + δ ≠ 0 := by
    linarith
  constructor
  · intro hw
    rcases hw with ⟨hw_unit, hratio⟩
    have hden_ne : Complex.normSq (1 + w) ≠ 0 := by
      intro hden
      have : (0 : ℝ) = δ := by
        simpa [hden] using hratio
      linarith
    have hmain : 1 - Complex.normSq w = δ * Complex.normSq (1 + w) := by
      exact (div_eq_iff hden_ne).mp hratio
    have hmain' : 1 - Complex.normSq w = δ * (Complex.normSq w + 1 + 2 * Complex.re w) := by
      rw [normSq_add_one] at hmain
      exact hmain
    refine ⟨hw_unit, ?_⟩
    rw [normSq_add_real]
    field_simp [hδ1_ne]
    nlinarith [hmain']
  · intro hw
    rcases hw with ⟨hw_unit, hcircle⟩
    have hplus_ne : 1 + w ≠ 0 := by
      intro hplus
      have hre : Complex.re w = -1 := by
        have h := congrArg Complex.re hplus
        simp at h
        linarith
      have him : Complex.im w = 0 := by
        have h := congrArg Complex.im hplus
        simp at h
        exact h
      have hnorm : Complex.normSq w = 1 := by
        simp [Complex.normSq_apply, hre, him]
      linarith
    have hden_ne : Complex.normSq (1 + w) ≠ 0 := (Complex.normSq_pos.2 hplus_ne).ne'
    have hcircle' :
        Complex.normSq w + (δ / (1 + δ)) ^ 2 + 2 * (δ / (1 + δ)) * Complex.re w =
          (1 / (1 + δ)) ^ 2 := by
      rw [normSq_add_real] at hcircle
      exact hcircle
    have hmain : 1 - Complex.normSq w = δ * Complex.normSq (1 + w) := by
      field_simp [hδ1_ne] at hcircle'
      nlinarith [hcircle', normSq_add_one w]
    refine ⟨hw_unit, ?_⟩
    exact (div_eq_iff hden_ne).2 hmain

end Omega.UnitCirclePhaseArithmetic
