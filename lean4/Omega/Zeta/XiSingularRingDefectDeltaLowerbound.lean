import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

lemma xi_singular_ring_defect_delta_lowerbound_single
    {β γ : ℝ} (hβ : β < (1 / 2 : ℝ)) (hρ : 0 < β ^ 2 + γ ^ 2) :
    let δ : ℝ := (1 / 2 : ℝ) - β
    (1 / 2 : ℝ) * Real.log (((1 - β) ^ 2 + γ ^ 2) / (β ^ 2 + γ ^ 2)) =
        (1 / 2 : ℝ) * Real.log (1 + 2 * δ / (β ^ 2 + γ ^ 2)) ∧
      δ / (β ^ 2 + γ ^ 2 + 2 * δ) ≤
        (1 / 2 : ℝ) * Real.log (((1 - β) ^ 2 + γ ^ 2) / (β ^ 2 + γ ^ 2)) := by
  let δ : ℝ := (1 / 2 : ℝ) - β
  let d : ℝ := β ^ 2 + γ ^ 2
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    linarith
  have hd_pos : 0 < d := hρ
  have hd_ne : d ≠ 0 := ne_of_gt hd_pos
  have hratio : (((1 - β) ^ 2 + γ ^ 2) / d : ℝ) = 1 + 2 * δ / d := by
    dsimp [d, δ]
    field_simp [hd_ne]
    ring
  have hx_nonneg : 0 ≤ 2 * δ / d := by positivity
  have hx_lower : 2 * (2 * δ / d) / ((2 * δ / d) + 2) ≤ Real.log (1 + 2 * δ / d) :=
    Real.le_log_one_add_of_nonneg hx_nonneg
  have hfrac :
      2 * (2 * δ / d) / ((2 * δ / d) + 2) = 2 * (δ / (d + δ)) := by
    have hdδ_ne : d + δ ≠ 0 := by positivity
    field_simp [hd_ne, hdδ_ne]
    ring
  have hstrong : δ / (d + δ) ≤ (1 / 2 : ℝ) * Real.log (1 + 2 * δ / d) := by
    rw [hfrac] at hx_lower
    linarith
  have hcompare_inv : (d + 2 * δ)⁻¹ ≤ (d + δ)⁻¹ := by
    exact (inv_le_inv₀ (by positivity) (by positivity)).2 (by nlinarith)
  have hcompare : δ / (d + 2 * δ) ≤ δ / (d + δ) := by
    have := mul_le_mul_of_nonneg_left hcompare_inv hδ_pos.le
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  have hratio_log :
      (1 / 2 : ℝ) * Real.log (((1 - β) ^ 2 + γ ^ 2) / d) =
        (1 / 2 : ℝ) * Real.log (1 + 2 * δ / d) := by
    exact congrArg (fun x : ℝ => (1 / 2 : ℝ) * Real.log x) hratio
  refine ⟨by simpa [δ, d] using hratio_log, ?_⟩
  have hmain : δ / (d + 2 * δ) ≤ (1 / 2 : ℝ) * Real.log (((1 - β) ^ 2 + γ ^ 2) / d) := by
    calc
      δ / (d + 2 * δ) ≤ δ / (d + δ) := hcompare
      _ ≤ (1 / 2 : ℝ) * Real.log (1 + 2 * δ / d) := hstrong
      _ = (1 / 2 : ℝ) * Real.log (((1 - β) ^ 2 + γ ^ 2) / d) := by
        simpa using hratio_log.symm
  simpa [δ, d] using hmain

lemma xi_singular_ring_defect_delta_lowerbound_sum
    {ι : Type*} (s : Finset ι) (β γ : ι → ℝ)
    (hβ : ∀ i ∈ s, β i < (1 / 2 : ℝ)) (hρ : ∀ i ∈ s, 0 < β i ^ 2 + γ i ^ 2) :
    s.sum (fun i => ((1 / 2 : ℝ) - β i) / (β i ^ 2 + γ i ^ 2 + 2 * ((1 / 2 : ℝ) - β i))) ≤
      s.sum (fun i => (1 / 2 : ℝ) * Real.log (((1 - β i) ^ 2 + γ i ^ 2) / (β i ^ 2 + γ i ^ 2))) := by
  exact
    Finset.sum_le_sum fun i hi =>
      (xi_singular_ring_defect_delta_lowerbound_single (hβ i hi) (hρ i hi)).2

lemma xi_singular_ring_defect_delta_lowerbound_sum_simplified
    {ι : Type*} (s : Finset ι) (β γ : ι → ℝ)
    (hβ_nonneg : ∀ i ∈ s, 0 ≤ β i) (hβ_lt : ∀ i ∈ s, β i < (1 / 2 : ℝ))
    (hρ : ∀ i ∈ s, 0 < β i ^ 2 + γ i ^ 2) :
    s.sum (fun i => ((1 / 2 : ℝ) - β i) / (β i ^ 2 + γ i ^ 2 + 1)) ≤
      s.sum (fun i => (1 / 2 : ℝ) * Real.log (((1 - β i) ^ 2 + γ i ^ 2) / (β i ^ 2 + γ i ^ 2))) := by
  calc
    s.sum (fun i => ((1 / 2 : ℝ) - β i) / (β i ^ 2 + γ i ^ 2 + 1)) ≤
        s.sum (fun i => ((1 / 2 : ℝ) - β i) / (β i ^ 2 + γ i ^ 2 + 2 * ((1 / 2 : ℝ) - β i))) := by
          refine Finset.sum_le_sum ?_
          intro i hi
          have hδ_nonneg : 0 ≤ (1 / 2 : ℝ) - β i := by linarith [hβ_nonneg i hi, hβ_lt i hi]
          have hδ_pos : 0 < (1 / 2 : ℝ) - β i := by linarith [hβ_lt i hi]
          have hden_cmp : β i ^ 2 + γ i ^ 2 + 2 * ((1 / 2 : ℝ) - β i) ≤ β i ^ 2 + γ i ^ 2 + 1 := by
            nlinarith [hβ_nonneg i hi, hβ_lt i hi]
          have hden_small_pos : 0 < β i ^ 2 + γ i ^ 2 + 2 * ((1 / 2 : ℝ) - β i) := by
            nlinarith [hρ i hi, hδ_pos]
          have hden_big_pos : 0 < β i ^ 2 + γ i ^ 2 + 1 := by
            positivity
          have hcompare_inv :
              (β i ^ 2 + γ i ^ 2 + 1)⁻¹ ≤ (β i ^ 2 + γ i ^ 2 + 2 * ((1 / 2 : ℝ) - β i))⁻¹ := by
            exact (inv_le_inv₀ hden_big_pos hden_small_pos).2 hden_cmp
          have := mul_le_mul_of_nonneg_left hcompare_inv hδ_nonneg
          simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    _ ≤ s.sum (fun i => (1 / 2 : ℝ) * Real.log (((1 - β i) ^ 2 + γ i ^ 2) / (β i ^ 2 + γ i ^ 2))) :=
      xi_singular_ring_defect_delta_lowerbound_sum s β γ hβ_lt hρ

/-- Paper label: `prop:xi-singular-ring-defect-delta-lowerbound`. -/
theorem paper_xi_singular_ring_defect_delta_lowerbound :
    (∀ β γ : ℝ, β < (1 / 2 : ℝ) → 0 < β ^ 2 + γ ^ 2 →
      let δ : ℝ := (1 / 2 : ℝ) - β
      (1 / 2 : ℝ) * Real.log (((1 - β) ^ 2 + γ ^ 2) / (β ^ 2 + γ ^ 2)) =
          (1 / 2 : ℝ) * Real.log (1 + 2 * δ / (β ^ 2 + γ ^ 2)) ∧
        δ / (β ^ 2 + γ ^ 2 + 2 * δ) ≤
          (1 / 2 : ℝ) * Real.log (((1 - β) ^ 2 + γ ^ 2) / (β ^ 2 + γ ^ 2))) ∧
      (∀ {ι : Type*} (s : Finset ι) (β γ : ι → ℝ),
        (∀ i ∈ s, β i < (1 / 2 : ℝ)) →
        (∀ i ∈ s, 0 < β i ^ 2 + γ i ^ 2) →
        s.sum (fun i => ((1 / 2 : ℝ) - β i) / (β i ^ 2 + γ i ^ 2 + 2 * ((1 / 2 : ℝ) - β i))) ≤
          s.sum
            (fun i => (1 / 2 : ℝ) * Real.log (((1 - β i) ^ 2 + γ i ^ 2) / (β i ^ 2 + γ i ^ 2)))) ∧
      (∀ {ι : Type*} (s : Finset ι) (β γ : ι → ℝ),
        (∀ i ∈ s, 0 ≤ β i) →
        (∀ i ∈ s, β i < (1 / 2 : ℝ)) →
        (∀ i ∈ s, 0 < β i ^ 2 + γ i ^ 2) →
        s.sum (fun i => ((1 / 2 : ℝ) - β i) / (β i ^ 2 + γ i ^ 2 + 1)) ≤
          s.sum
            (fun i => (1 / 2 : ℝ) * Real.log (((1 - β i) ^ 2 + γ i ^ 2) / (β i ^ 2 + γ i ^ 2)))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro β γ hβ hρ
    exact xi_singular_ring_defect_delta_lowerbound_single hβ hρ
  · intro ι s β γ hβ hρ
    exact xi_singular_ring_defect_delta_lowerbound_sum s β γ hβ hρ
  · intro ι s β γ hβ_nonneg hβ_lt hρ
    exact xi_singular_ring_defect_delta_lowerbound_sum_simplified s β γ hβ_nonneg hβ_lt hρ

end Omega.Zeta
