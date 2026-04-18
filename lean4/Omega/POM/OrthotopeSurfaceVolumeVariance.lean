import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic

namespace Omega.POM

/-- The normalized surface-to-volume ratio of a two-axis orthotope with side lengths `a`, `b`.
For a rectangle this is `S / (2V) = (1 / a + 1 / b) / 2`. -/
noncomputable def orthotopeSurfaceVolumeRatio2 (a b : ℝ) : ℝ :=
  ((1 / a) + (1 / b)) / 2

private lemma orthotopeSurfaceVolumeRatio2_eq_cosh_log
    {a b : ℝ} (ha : 0 < a) (hvol : a * b = 1) :
    orthotopeSurfaceVolumeRatio2 a b = Real.cosh (Real.log a) := by
  have hb_pos : 0 < b := by
    nlinarith
  have hb_eq : b = a⁻¹ := by
    have hab_inv : a = b⁻¹ := by
      rw [inv_eq_one_div]
      exact (eq_div_iff (ne_of_gt hb_pos)).2 hvol
    have hinv := congrArg Inv.inv hab_inv
    simpa using hinv.symm
  unfold orthotopeSurfaceVolumeRatio2
  simp [hb_eq, Real.cosh_log ha]
  ring

private lemma cosh_lower_quadratic (x : ℝ) : 1 + x ^ 2 / 2 ≤ Real.cosh x := by
  have hsq :
      (x / 2) ^ 2 ≤ Real.sinh (x / 2) ^ 2 := by
    have habs : |x / 2| ≤ |Real.sinh (x / 2)| := by
      rw [Real.abs_sinh]
      exact (Real.self_le_sinh_iff).2 (abs_nonneg (x / 2))
    have hsqabs : |x / 2| ^ 2 ≤ |Real.sinh (x / 2)| ^ 2 := by
      simpa [abs_abs] using (sq_le_sq.2 habs)
    simpa [sq_abs] using hsqabs
  have hcosh :
      Real.cosh x = 1 + 2 * Real.sinh (x / 2) ^ 2 := by
    calc
      Real.cosh x = Real.cosh (2 * (x / 2)) := by ring_nf
      _ = 1 + 2 * Real.sinh (x / 2) ^ 2 := by
            rw [Real.cosh_two_mul, Real.cosh_sq']
            ring
  calc
    1 + x ^ 2 / 2 = 1 + 2 * (x / 2) ^ 2 := by ring
    _ ≤ 1 + 2 * Real.sinh (x / 2) ^ 2 := by gcongr
    _ = Real.cosh x := hcosh.symm

/-- For a two-axis orthotope with normalized volume `ab = 1`, the surface-to-volume ratio is the
average of `exp (-log a)` and `exp (-log b)`, hence it dominates the logarithmic variance term.
Equality in the Jensen/strict-convexity regime forces the two side lengths to coincide.
    thm:pom-orthotope-surface-volume-variance -/
theorem paper_pom_orthotope_surface_volume_variance
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hvol : a * b = 1) :
    1 + (Real.log a - Real.log b) ^ 2 / 8 ≤ orthotopeSurfaceVolumeRatio2 a b ∧
      (orthotopeSurfaceVolumeRatio2 a b = 1 ↔ a = b) := by
  have ha_ne : a ≠ 0 := ne_of_gt ha
  have hb_eq : b = a⁻¹ := by
    have hab_inv : a = b⁻¹ := by
      rw [inv_eq_one_div]
      exact (eq_div_iff (ne_of_gt hb)).2 hvol
    have hinv := congrArg Inv.inv hab_inv
    simpa using hinv.symm
  have hlogb : Real.log b = -Real.log a := by
    rw [hb_eq, Real.log_inv]
  have hratio :
      orthotopeSurfaceVolumeRatio2 a b = Real.cosh (Real.log a) :=
    orthotopeSurfaceVolumeRatio2_eq_cosh_log ha hvol
  have hlower :
      1 + (Real.log a) ^ 2 / 2 ≤ orthotopeSurfaceVolumeRatio2 a b := by
    calc
      1 + (Real.log a) ^ 2 / 2 ≤ Real.cosh (Real.log a) := cosh_lower_quadratic (Real.log a)
      _ = orthotopeSurfaceVolumeRatio2 a b := hratio.symm
  have hvariance :
      1 + (Real.log a - Real.log b) ^ 2 / 8 = 1 + (Real.log a) ^ 2 / 2 := by
    rw [hlogb]
    ring
  refine ⟨by simpa [hvariance] using hlower, ?_⟩
  constructor
  · intro hratio_one
    have hsum : a + b = 2 := by
      unfold orthotopeSurfaceVolumeRatio2 at hratio_one
      have hba : 1 / a = b := by
        rw [div_eq_iff ha_ne]
        simpa [mul_comm] using hvol.symm
      have hab : 1 / b = a := by
        rw [div_eq_iff (ne_of_gt hb)]
        simpa [mul_comm] using hvol.symm
      rw [hba, hab] at hratio_one
      linarith
    have ha_one : a = 1 := by
      nlinarith [sq_nonneg (a - 1), hsum, hvol]
    have hb_one : b = 1 := by
      nlinarith [hvol, ha_one]
    nlinarith [ha_one, hb_one]
  · intro hab
    have ha_one : a = 1 := by
      nlinarith [hvol, hab, ha]
    have hb_one : b = 1 := by
      nlinarith [hvol, ha_one]
    unfold orthotopeSurfaceVolumeRatio2
    simp [ha_one, hb_one]

end Omega.POM
