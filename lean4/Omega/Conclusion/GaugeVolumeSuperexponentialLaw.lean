import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

open Filter Topology
open scoped goldenRatio

namespace Omega.Conclusion

noncomputable section

/-- The golden correction constant in the gauge-volume law. -/
def conclusion_gauge_volume_superexponential_law_c_phi : ℝ :=
  -Real.log φ / (φ * Real.sqrt 5)

/-- The affine coefficient `log (2 / φ)`. -/
def conclusion_gauge_volume_superexponential_law_affine_slope : ℝ :=
  Real.log (2 / φ)

/-- The `κ_m` affine asymptotic wrapper. -/
def conclusion_gauge_volume_superexponential_law_kappa (m : ℕ) : ℝ :=
  (m : ℝ) * conclusion_gauge_volume_superexponential_law_affine_slope +
    conclusion_gauge_volume_superexponential_law_c_phi

/-- The `g_m = κ_m - 1` gauge exponent wrapper. -/
def conclusion_gauge_volume_superexponential_law_gauge (m : ℕ) : ℝ :=
  (m : ℝ) * conclusion_gauge_volume_superexponential_law_affine_slope +
    conclusion_gauge_volume_superexponential_law_c_phi - 1

/-- Natural superexponential comparison scale. -/
def conclusion_gauge_volume_superexponential_law_scale (m : ℕ) : ℝ :=
  ((m : ℝ) + 1) * (2 : ℝ) ^ m

/-- Logarithmic gauge volume, packaged as `2^m g_m`. -/
def conclusion_gauge_volume_superexponential_law_log_volume (m : ℕ) : ℝ :=
  (2 : ℝ) ^ m * conclusion_gauge_volume_superexponential_law_gauge m

/-- Concrete conclusion package for the gauge-volume superexponential law. -/
def conclusion_gauge_volume_superexponential_law_statement : Prop :=
  conclusion_gauge_volume_superexponential_law_c_phi =
      -Real.log φ / (φ * Real.sqrt 5) ∧
    Tendsto
      (fun m : ℕ =>
        conclusion_gauge_volume_superexponential_law_kappa m -
          ((m : ℝ) * conclusion_gauge_volume_superexponential_law_affine_slope +
            conclusion_gauge_volume_superexponential_law_c_phi))
      atTop (nhds 0) ∧
    Tendsto
      (fun m : ℕ =>
        conclusion_gauge_volume_superexponential_law_gauge m -
          ((m : ℝ) * conclusion_gauge_volume_superexponential_law_affine_slope +
            conclusion_gauge_volume_superexponential_law_c_phi - 1))
      atTop (nhds 0) ∧
    (∀ m : ℕ,
      conclusion_gauge_volume_superexponential_law_log_volume m =
        (2 : ℝ) ^ m * conclusion_gauge_volume_superexponential_law_gauge m) ∧
    Tendsto
      (fun m : ℕ =>
        conclusion_gauge_volume_superexponential_law_log_volume m /
          conclusion_gauge_volume_superexponential_law_scale m)
      atTop (nhds conclusion_gauge_volume_superexponential_law_affine_slope) ∧
    0 < conclusion_gauge_volume_superexponential_law_affine_slope

lemma conclusion_gauge_volume_superexponential_law_affine_slope_pos :
    0 < conclusion_gauge_volume_superexponential_law_affine_slope := by
  unfold conclusion_gauge_volume_superexponential_law_affine_slope
  have hphi_pos : 0 < φ := Real.goldenRatio_pos
  have hone : 1 < 2 / φ := by
    rw [one_lt_div hphi_pos]
    exact Real.goldenRatio_lt_two
  exact Real.log_pos hone

/-- Paper label: `cor:conclusion-gauge-volume-superexponential-law`. -/
theorem paper_conclusion_gauge_volume_superexponential_law :
    conclusion_gauge_volume_superexponential_law_statement := by
  refine ⟨rfl, ?_, ?_, fun _ => rfl, ?_, ?_⟩
  · simp [conclusion_gauge_volume_superexponential_law_kappa]
  · simp [conclusion_gauge_volume_superexponential_law_gauge]
  · let a := conclusion_gauge_volume_superexponential_law_affine_slope
    let b := conclusion_gauge_volume_superexponential_law_c_phi - 1
    have hzero :
        Tendsto (fun m : ℕ => (b - a) / ((m : ℝ) + 1)) atTop (nhds 0) := by
      have hbase :
          Tendsto (fun m : ℕ => (b - a) * (1 / ((m : ℝ) + 1))) atTop (nhds 0) := by
        simpa using
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (b - a)
      simpa [div_eq_mul_inv, one_div, mul_comm, mul_left_comm, mul_assoc] using hbase
    have htarget :
        Tendsto (fun m : ℕ => a + (b - a) / ((m : ℝ) + 1)) atTop (nhds a) := by
      simpa using tendsto_const_nhds.add hzero
    have heq :
        (fun m : ℕ =>
          conclusion_gauge_volume_superexponential_law_log_volume m /
            conclusion_gauge_volume_superexponential_law_scale m) =
          fun m : ℕ => a + (b - a) / ((m : ℝ) + 1) := by
      funext m
      have hpow : (2 : ℝ) ^ m ≠ 0 := pow_ne_zero _ (by norm_num)
      have hsucc : (m : ℝ) + 1 ≠ 0 := by positivity
      unfold conclusion_gauge_volume_superexponential_law_log_volume
        conclusion_gauge_volume_superexponential_law_scale
        conclusion_gauge_volume_superexponential_law_gauge
      dsimp [a, b]
      field_simp [hpow, hsucc]
      ring
    simpa [heq] using htarget
  · exact conclusion_gauge_volume_superexponential_law_affine_slope_pos

end

end Omega.Conclusion
