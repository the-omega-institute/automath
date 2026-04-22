import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
import Omega.Zeta.AppOffcriticalRadiusCompression

namespace Omega.Zeta

/-- The disk-pole modulus is the square root of the closed-form Cayley modulus squared. -/
noncomputable def xi_toeplitz_diskpole_modulus_closed_form_high_height_modulus
    (γ δ : ℝ) : ℝ :=
  Real.sqrt (appOffcriticalModSq γ δ)

/-- High-height closed forms for the disk-pole modulus: the squared modulus has the exact Cayley
formula, `1-|a|²` is the boundary depth, and `1-|a|` is controlled by `δ/γ²` once `|γ| ≥ 1`.
    prop:xi-toeplitz-diskpole-modulus-closed-form-high-height -/
  theorem paper_xi_toeplitz_diskpole_modulus_closed_form_high_height
    (γ δ : ℝ) (hδ : 0 < δ) (hγ : 1 ≤ |γ|) :
    let r := xi_toeplitz_diskpole_modulus_closed_form_high_height_modulus γ δ
    r ^ 2 = (γ ^ 2 + (δ - 1) ^ 2) / (γ ^ 2 + (δ + 1) ^ 2) ∧
      1 - r ^ 2 = 4 * δ / (γ ^ 2 + (δ + 1) ^ 2) ∧
      1 - r = (4 * δ / (γ ^ 2 + (δ + 1) ^ 2)) / (1 + r) ∧
      1 - r ≤ 4 * δ / (γ ^ 2) := by
  let r := xi_toeplitz_diskpole_modulus_closed_form_high_height_modulus γ δ
  have hmodsq_nonneg : 0 ≤ appOffcriticalModSq γ δ := by
    unfold appOffcriticalModSq CayleyDepthIdentity.cayleyModSq
    positivity
  have hr_nonneg : 0 ≤ r := by
    simp [r, xi_toeplitz_diskpole_modulus_closed_form_high_height_modulus]
  have hr_sq :
      r ^ 2 = appOffcriticalModSq γ δ := by
    simp [r, xi_toeplitz_diskpole_modulus_closed_form_high_height_modulus, hmodsq_nonneg]
  have hsq_closed :
      r ^ 2 = (γ ^ 2 + (δ - 1) ^ 2) / (γ ^ 2 + (δ + 1) ^ 2) := by
    rw [hr_sq, appOffcriticalModSq_closed_form]
  have hone_sub_sq :
      1 - r ^ 2 = 4 * δ / (γ ^ 2 + (δ + 1) ^ 2) := by
    calc
      1 - r ^ 2 = 1 - appOffcriticalModSq γ δ := by rw [hr_sq]
      _ = appOffcriticalBoundaryDepth γ δ := by
        rfl
      _ = 4 * δ / (γ ^ 2 + (δ + 1) ^ 2) := appOffcriticalBoundaryDepth_closed_form γ δ hδ
  have hγ_ne : γ ≠ 0 := by
    intro hzero
    have : (1 : ℝ) ≤ 0 := by simpa [hzero] using hγ
    linarith
  have hγsq_pos : 0 < γ ^ 2 := by
    exact sq_pos_of_ne_zero hγ_ne
  have h_one_add_r_ne : 1 + r ≠ 0 := by
    linarith
  have hone_sub :
      1 - r = (4 * δ / (γ ^ 2 + (δ + 1) ^ 2)) / (1 + r) := by
    calc
      1 - r = (1 - r ^ 2) / (1 + r) := by
        field_simp [h_one_add_r_ne]
        ring
      _ = (4 * δ / (γ ^ 2 + (δ + 1) ^ 2)) / (1 + r) := by rw [hone_sub_sq]
  have hnum_nonneg : 0 ≤ 4 * δ / (γ ^ 2 + (δ + 1) ^ 2) := by
    have hnum_pos : 0 < 4 * δ := by nlinarith
    have hden_pos : 0 < γ ^ 2 + (δ + 1) ^ 2 := by positivity
    exact div_nonneg hnum_pos.le hden_pos.le
  have hdrop_one_plus :
      (4 * δ / (γ ^ 2 + (δ + 1) ^ 2)) / (1 + r) ≤ 4 * δ / (γ ^ 2 + (δ + 1) ^ 2) := by
    have h_one_le : 1 ≤ 1 + r := by linarith
    exact div_le_self hnum_nonneg h_one_le
  have hgamma_denom :
      γ ^ 2 ≤ γ ^ 2 + (δ + 1) ^ 2 := by
    nlinarith [sq_nonneg (δ + 1)]
  have hhigh_height :
      4 * δ / (γ ^ 2 + (δ + 1) ^ 2) ≤ 4 * δ / (γ ^ 2) := by
    have hnum_nonneg' : 0 ≤ 4 * δ := by linarith
    exact div_le_div_of_nonneg_left hnum_nonneg' hγsq_pos hgamma_denom
  refine ⟨hsq_closed, hone_sub_sq, hone_sub, ?_⟩
  calc
    1 - r = (4 * δ / (γ ^ 2 + (δ + 1) ^ 2)) / (1 + r) := hone_sub
    _ ≤ 4 * δ / (γ ^ 2 + (δ + 1) ^ 2) := hdrop_one_plus
    _ ≤ 4 * δ / (γ ^ 2) := hhigh_height

end Omega.Zeta
