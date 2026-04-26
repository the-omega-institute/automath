import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

namespace Omega.POM

open Filter
open scoped Topology

/-- The golden ratio. -/
noncomputable def pom_aitken_window_golden_invariance_phi : ℝ :=
  (1 + Real.sqrt 5) / 2

/-- Its reciprocal, the expected Aitken error-scale limit. -/
noncomputable def pom_aitken_window_golden_invariance_phi_inv : ℝ :=
  1 / pom_aitken_window_golden_invariance_phi

lemma pom_aitken_window_golden_invariance_phi_pos :
    0 < pom_aitken_window_golden_invariance_phi := by
  have hsqrt : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  dsimp [pom_aitken_window_golden_invariance_phi]
  nlinarith

lemma pom_aitken_window_golden_invariance_phi_gt_one :
    1 < pom_aitken_window_golden_invariance_phi := by
  have hsq : (Real.sqrt 5) ^ 2 = 5 := by
    have hfive_nonneg : (0 : ℝ) ≤ 5 := by
      norm_num
    simp [pow_two, hfive_nonneg]
  have hsqrt_nonneg : 0 ≤ Real.sqrt 5 := by
    positivity
  dsimp [pom_aitken_window_golden_invariance_phi]
  nlinarith

lemma pom_aitken_window_golden_invariance_phi_ne_zero :
    pom_aitken_window_golden_invariance_phi ≠ 0 :=
  ne_of_gt pom_aitken_window_golden_invariance_phi_pos

lemma pom_aitken_window_golden_invariance_phi_inv_ne_zero :
    pom_aitken_window_golden_invariance_phi_inv ≠ 0 := by
  simp [pom_aitken_window_golden_invariance_phi_inv,
    pom_aitken_window_golden_invariance_phi_ne_zero]

lemma pom_aitken_window_golden_invariance_phi_log_ne_zero :
    Real.log pom_aitken_window_golden_invariance_phi ≠ 0 := by
  exact
    (Real.log_ne_zero).2
      ⟨pom_aitken_window_golden_invariance_phi_ne_zero,
        ne_of_gt pom_aitken_window_golden_invariance_phi_gt_one, by
          linarith [pom_aitken_window_golden_invariance_phi_pos]⟩

/-- Concrete package for the Aitken-window asymptotic. -/
structure pom_aitken_window_golden_invariance_data where
  tol : ℝ
  delta_ait : ℕ → ℝ
  tol_pos : 0 < tol
  tol_lt_one : tol < 1
  delta_ait_pos : ∀ n, 0 < delta_ait n
  delta_ait_limit :
    Tendsto delta_ait atTop (𝓝 pom_aitken_window_golden_invariance_phi_inv)

namespace pom_aitken_window_golden_invariance_data

/-- Window length extracted from the preceding Aitken audit remark. -/
noncomputable def window_length (D : pom_aitken_window_golden_invariance_data) (n : ℕ) : ℝ :=
  Real.log (1 / D.tol) / Real.log (1 / D.delta_ait n)

/-- The golden-ratio asymptotic predicted by the limiting Aitken error scale. -/
def golden_window_asymptotic (D : pom_aitken_window_golden_invariance_data) : Prop :=
  Tendsto D.window_length atTop
    (𝓝 (Real.log (1 / D.tol) / Real.log pom_aitken_window_golden_invariance_phi))

end pom_aitken_window_golden_invariance_data

/-- Paper label: `cor:pom-aitken-window-golden-invariance`. -/
theorem paper_pom_aitken_window_golden_invariance
    (D : pom_aitken_window_golden_invariance_data) :
    D.golden_window_asymptotic := by
  have hInv :
      Tendsto (fun n : ℕ => 1 / D.delta_ait n) atTop
        (𝓝 pom_aitken_window_golden_invariance_phi) := by
    have hInv' :
        Tendsto (fun n : ℕ => (D.delta_ait n)⁻¹) atTop
          (𝓝 (pom_aitken_window_golden_invariance_phi_inv)⁻¹) :=
      D.delta_ait_limit.inv₀ pom_aitken_window_golden_invariance_phi_inv_ne_zero
    simpa [one_div, pom_aitken_window_golden_invariance_phi_inv,
      pom_aitken_window_golden_invariance_phi_ne_zero] using hInv'
  have hDen :
      Tendsto (fun n : ℕ => Real.log (1 / D.delta_ait n)) atTop
        (𝓝 (Real.log pom_aitken_window_golden_invariance_phi)) := by
    exact
      (Real.continuousAt_log pom_aitken_window_golden_invariance_phi_ne_zero).tendsto.comp hInv
  have hNum :
      Tendsto (fun _ : ℕ => Real.log (1 / D.tol)) atTop (𝓝 (Real.log (1 / D.tol))) :=
    tendsto_const_nhds
  change Tendsto
      (fun n : ℕ => Real.log (1 / D.tol) / Real.log (1 / D.delta_ait n)) atTop
      (𝓝 (Real.log (1 / D.tol) / Real.log pom_aitken_window_golden_invariance_phi))
  exact hNum.div hDen pom_aitken_window_golden_invariance_phi_log_ne_zero

end Omega.POM
