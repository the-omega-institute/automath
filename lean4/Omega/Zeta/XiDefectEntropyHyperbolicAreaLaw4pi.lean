import Mathlib.Probability.Distributions.Cauchy
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

theorem paper_xi_defect_entropy_hyperbolic_area_law_4pi {ι : Type} [Fintype ι] (γ δ : ι → ℝ)
    (m : ι → ℕ) (hδ : ∀ i, 0 < δ i) :
    (∑ i, (m i : ℝ) * (δ i / (1 + δ i))) =
      (1 / (4 * Real.pi)) *
        ∑ i, ∫ x : ℝ, (m i : ℝ) * (4 * δ i) / (((x - γ i)^2) + (1 + δ i)^2) := by
  have hterm :
      ∀ i,
        (1 / (4 * Real.pi)) *
            ∫ x : ℝ, (m i : ℝ) * (4 * δ i) / (((x - γ i)^2) + (1 + δ i)^2) =
          (m i : ℝ) * (δ i / (1 + δ i)) := by
    intro i
    let σ : NNReal := ⟨1 + δ i, by linarith [hδ i]⟩
    have hσ_pos : 0 < σ := by
      change 0 < 1 + δ i
      linarith [hδ i]
    have hσ_ne : σ ≠ 0 := by
      exact ne_of_gt hσ_pos
    have hexpr :
        (fun x : ℝ => (m i : ℝ) * (4 * δ i) / (((x - γ i)^2) + (1 + δ i)^2)) =
          fun x : ℝ =>
            (4 * Real.pi * ((m i : ℝ) * (δ i / (1 + δ i)))) *
              Probability.cauchyPDFReal (γ i) σ x := by
      funext x
      rw [Probability.cauchyPDFReal_def]
      simp [σ, div_eq_mul_inv]
      field_simp [Real.pi_ne_zero, (show (1 + δ i) ≠ 0 by linarith [hδ i])]
    calc
      (1 / (4 * Real.pi)) *
            ∫ x : ℝ, (m i : ℝ) * (4 * δ i) / (((x - γ i)^2) + (1 + δ i)^2) =
          (1 / (4 * Real.pi)) *
            ∫ x : ℝ,
              (4 * Real.pi * ((m i : ℝ) * (δ i / (1 + δ i)))) *
                Probability.cauchyPDFReal (γ i) σ x := by
                  rw [hexpr]
      _ = (1 / (4 * Real.pi)) *
            ((4 * Real.pi * ((m i : ℝ) * (δ i / (1 + δ i)))) *
              ∫ x : ℝ, Probability.cauchyPDFReal (γ i) σ x) := by
                rw [MeasureTheory.integral_const_mul]
      _ = (1 / (4 * Real.pi)) * (4 * Real.pi * ((m i : ℝ) * (δ i / (1 + δ i)))) := by
            rw [Probability.integral_cauchyPDFReal (x₀ := γ i) hσ_ne, mul_one]
      _ = (m i : ℝ) * (δ i / (1 + δ i)) := by
            have h4pi_ne : (4 * Real.pi : ℝ) ≠ 0 := by positivity
            field_simp [h4pi_ne]
  symm
  calc
    (1 / (4 * Real.pi)) *
          ∑ i, ∫ x : ℝ, (m i : ℝ) * (4 * δ i) / (((x - γ i)^2) + (1 + δ i)^2) =
        ∑ i, (1 / (4 * Real.pi)) *
          ∫ x : ℝ, (m i : ℝ) * (4 * δ i) / (((x - γ i)^2) + (1 + δ i)^2) := by
            rw [Finset.mul_sum]
    _ = ∑ i, (m i : ℝ) * (δ i / (1 + δ i)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            exact hterm i
    _ = (∑ i, (m i : ℝ) * (δ i / (1 + δ i))) := rfl

end Omega.Zeta
