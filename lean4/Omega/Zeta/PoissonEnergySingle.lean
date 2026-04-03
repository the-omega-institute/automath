import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic

open Filter
open scoped Topology

namespace Omega.Zeta

/-- Single-defect Poisson `L²` energy rational identity.
    cor:xi-finite-defect-poisson-l2-energy-single-defect -/
theorem singleDefectEnergy_rational_identity (t δ : ℚ)
    (ht : t + 1 ≠ 0)
    (hminus : t + 1 - δ ≠ 0)
    (hplus : t + 1 + δ ≠ 0) :
    (1 / (2 * (t + 1 - δ)) + 1 / (2 * (t + 1 + δ)) - 1 / (t + 1)) =
      δ^2 / ((t + 1) * ((t + 1)^2 - δ^2)) := by
  have hquad : (t + 1)^2 - δ^2 ≠ 0 := by
    intro hq
    apply (mul_ne_zero hminus hplus)
    calc
      (t + 1 - δ) * (t + 1 + δ) = (t + 1)^2 - δ^2 := by ring
      _ = 0 := hq
  field_simp [ht, hminus, hplus, hquad]
  ring

/-- Nonnegativity of the quadratic numerator.
    cor:xi-finite-defect-poisson-l2-energy-single-defect -/
theorem singleDefectEnergy_nonneg_num (_t δ : ℚ) :
    0 ≤ δ^2 := by
  nlinarith

private lemma singleDefectEnergy_cubic_cancel
    {u δ : ℝ} (hu : u ≠ 0) (hquad : u ^ (2 : ℕ) - δ^2 ≠ 0) :
    u ^ (3 : ℕ) * (δ^2 / (u * (u ^ (2 : ℕ) - δ^2))) =
      δ^2 * (u ^ (2 : ℕ) / (u ^ (2 : ℕ) - δ^2)) := by
  have hu2 : u ^ (2 : ℕ) ≠ 0 := pow_ne_zero _ hu
  field_simp [hu, hu2, hquad]

private lemma singleDefectEnergy_square_ratio
    {u δ : ℝ} (hu : u ≠ 0) (hquad : u ^ (2 : ℕ) - δ^2 ≠ 0) :
    u ^ (2 : ℕ) / (u ^ (2 : ℕ) - δ^2) = 1 / (1 - δ^2 / u ^ (2 : ℕ)) := by
  have hu2 : u ^ (2 : ℕ) ≠ 0 := pow_ne_zero _ hu
  field_simp [hu, hu2, hquad]

/-- Cubic-limit form of the single-defect Poisson `L²` energy.
    cor:xi-finite-defect-poisson-l2-energy-single-defect -/
theorem singleDefectEnergy_cubic_limit (m δ : ℝ) :
    Tendsto (fun t : ℝ =>
      (t + 1) ^ (3 : ℕ) *
        (Real.pi * m^2 * (δ^2 / ((t + 1) * ((t + 1)^2 - δ^2))))
      ) atTop (𝓝 (Real.pi * (m * δ)^2)) := by
  let g : ℝ → ℝ := fun t => δ^2 / (t + 1) ^ (2 : ℕ)
  have hsq : Tendsto (fun t : ℝ => (t + 1) ^ (2 : ℕ)) atTop atTop := by
    exact (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp
      (tendsto_atTop_add_const_right _ _ tendsto_id)
  have h_inv : Tendsto (fun t : ℝ => ((t + 1) ^ (2 : ℕ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hsq
  have hg_eq : g = fun t : ℝ => δ^2 * (((t + 1) ^ (2 : ℕ))⁻¹) := by
    funext t
    simp [g, div_eq_mul_inv]
  have hg_zero : Tendsto g atTop (𝓝 0) := by
    rw [hg_eq]
    simpa using (tendsto_const_nhds (x := δ^2)).mul h_inv
  have hden : Tendsto (fun t : ℝ => 1 - g t) atTop (𝓝 1) := by
    simpa [sub_eq_add_neg] using tendsto_const_nhds.add (hg_zero.neg)
  have hinv : Tendsto (fun t : ℝ => (1 - g t)⁻¹) atTop (𝓝 ((1 : ℝ)⁻¹)) := by
    have hone : (1 : ℝ) ≠ 0 := by norm_num
    exact hden.inv₀ hone
  have hmain : Tendsto (fun t : ℝ => 1 / (1 - g t)) atTop (𝓝 1) := by
    simpa [one_div] using hinv
  have hrewrite : ∀ᶠ t : ℝ in atTop,
      (t + 1) ^ (3 : ℕ) *
          (Real.pi * m^2 * (δ^2 / ((t + 1) * ((t + 1)^2 - δ^2)))) =
        (Real.pi * (m * δ)^2) * (1 / (1 - g t)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_gt_atTop (|δ| - 1)] with t ht0 ht
    have habs_lt : |δ| < t + 1 := by linarith
    have ht1 : 0 < t + 1 := by linarith [abs_nonneg δ]
    have ht1_ne : (t + 1 : ℝ) ≠ 0 := ne_of_gt ht1
    have hsquare : δ ^ 2 < (t + 1) ^ 2 := by
      rw [sq_lt_sq]
      simpa [abs_of_nonneg ht1.le] using habs_lt
    have hlt : δ^2 < (t + 1) ^ (2 : ℕ) := by simpa [sq] using hsquare
    have hsq_ne : (t + 1) ^ (2 : ℕ) - δ^2 ≠ 0 := by linarith
    have hcancel :
        (t + 1) ^ (3 : ℕ) * (δ^2 / ((t + 1) * ((t + 1) ^ (2 : ℕ) - δ^2))) =
          δ^2 * ((t + 1) ^ (2 : ℕ) / ((t + 1) ^ (2 : ℕ) - δ^2)) :=
      singleDefectEnergy_cubic_cancel (u := t + 1) (δ := δ) ht1_ne hsq_ne
    have hratio :
        (t + 1) ^ (2 : ℕ) / ((t + 1) ^ (2 : ℕ) - δ^2) = 1 / (1 - g t) := by
      simpa [g] using singleDefectEnergy_square_ratio (u := t + 1) (δ := δ) ht1_ne hsq_ne
    calc
      (t + 1) ^ (3 : ℕ) *
          (Real.pi * m^2 * (δ^2 / ((t + 1) * ((t + 1)^2 - δ^2))))
          = Real.pi * m^2 * ((t + 1) ^ (3 : ℕ) *
              (δ^2 / ((t + 1) * ((t + 1)^2 - δ^2)))) := by ring
      _ = Real.pi * m^2 * (δ^2 * ((t + 1) ^ (2 : ℕ) / ((t + 1) ^ (2 : ℕ) - δ^2))) := by
            rw [hcancel]
      _ = Real.pi * (m * δ)^2 * ((t + 1) ^ (2 : ℕ) / ((t + 1) ^ (2 : ℕ) - δ^2)) := by
            ring_nf
      _ = Real.pi * (m * δ)^2 * (1 / (1 - g t)) := by rw [hratio]
  have htarget : Tendsto (fun t : ℝ => (Real.pi * (m * δ)^2) * (1 / (1 - g t))) atTop
      (𝓝 (Real.pi * (m * δ)^2)) := by
    have hconst : Tendsto (fun _ : ℝ => Real.pi * (m * δ)^2) atTop (𝓝 (Real.pi * (m * δ)^2)) :=
      tendsto_const_nhds
    simpa using hconst.mul hmain
  have heq :
      (fun t : ℝ => (Real.pi * (m * δ)^2) * (1 / (1 - g t))) =ᶠ[atTop]
      (fun t : ℝ =>
        (t + 1) ^ (3 : ℕ) *
          (Real.pi * m^2 * (δ^2 / ((t + 1) * ((t + 1)^2 - δ^2))))) := by
    filter_upwards [hrewrite] with t ht
    exact ht.symm
  exact Filter.Tendsto.congr' heq htarget

/-- Value at `t = 0` matches the quadratic single-defect form.
    cor:xi-finite-defect-poisson-l2-energy-single-defect -/
theorem singleDefectEnergy_zero (m δ : ℝ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    Real.pi * m^2 *
        (1 / (2 * (1 - δ)) + 1 / (2 * (1 + δ)) - 1) =
      Real.pi * m^2 * (δ^2 / (1 - δ^2)) := by
  have hden1 : (1 - δ : ℝ) ≠ 0 := by linarith
  have hden2 : (1 + δ : ℝ) ≠ 0 := by linarith [hδ0]
  have hden3 : (1 - δ ^ 2 : ℝ) ≠ 0 := by
    nlinarith [hδ0, hδ1]
  field_simp [hden1, hden2, hden3]
  ring

/-- Zero energy at `t = 0` forces the single defect to be trivial.
    prop:xi-finite-defect-poisson-l2-energy-zero-rigidity -/
theorem singleDefectEnergy_zero_rigidity_single (m δ : ℝ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    Real.pi * m^2 * (δ^2 / (1 - δ^2)) = 0 ↔ m = 0 ∨ δ = 0 := by
  have hzero := singleDefectEnergy_zero m δ hδ0 hδ1
  rw [← hzero]
  have hden : 0 < 1 - δ ^ 2 := by
    nlinarith [hδ0, hδ1]
  have hcoeff_ne : Real.pi * (1 / (1 - δ ^ 2)) ≠ 0 := by
    have hone : (1 / (1 - δ ^ 2)) ≠ 0 := by
      simpa [one_div] using (inv_ne_zero (ne_of_gt hden))
    exact mul_ne_zero (ne_of_gt Real.pi_pos) hone
  have hformula :
      Real.pi * m ^ 2 * (1 / (2 * (1 - δ)) + 1 / (2 * (1 + δ)) - 1) =
        (Real.pi * (1 / (1 - δ ^ 2))) * (m * δ) ^ 2 := by
    rw [hzero]
    ring
  rw [hformula]
  constructor
  · intro h
    have hsq_zero : (m * δ) ^ 2 = 0 := by
      exact (mul_eq_zero.mp h).resolve_left hcoeff_ne
    have hmul : m * δ = 0 := by
      exact eq_zero_of_pow_eq_zero hsq_zero
    exact mul_eq_zero.mp hmul
  · rintro (rfl | rfl) <;> simp

/-- Zero energy at `t = 0` is equivalent to vanishing mass or defect.
    prop:xi-finite-defect-poisson-l2-energy-zero-rigidity -/
theorem singleDefectEnergy_zero_eq_zero_iff
    (m δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    Real.pi * m^2 * (δ^2 / (1 - δ^2)) = 0 ↔ (m = 0 ∨ δ = 0) := by
  simpa using singleDefectEnergy_zero_rigidity_single m δ hδ0 hδ1

end Omega.Zeta
