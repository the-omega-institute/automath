import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Paper label: `cor:xi-cross-energy-lower-bound-by-min-separation`.

If every cross-distance is at least the minimum separation `rhoMin`, the cross-energy identity
gives a termwise lower bound. Rewriting the determinant identity then yields the corresponding
exponential compression estimate. -/
theorem paper_xi_cross_energy_lower_bound_by_min_separation {α β : Type*} [Fintype α]
    [Fintype β] (rho : α → β → ℝ) (rhoMin crossEnergy detA detB detUnion : ℝ)
    (hrho_pos : ∀ a b, 0 < rho a b) (hrho_le_min : ∀ a b, rho a b ≤ rhoMin)
    (hcross : crossEnergy = 2 * ∑ a, ∑ b, -Real.log (rho a b))
    (hdet : detUnion = detA * detB * Real.exp (-crossEnergy))
    (hdetProd_nonneg : 0 ≤ detA * detB) :
    2 * ((Fintype.card α : ℝ) * (Fintype.card β : ℝ)) * (-Real.log rhoMin) ≤
        crossEnergy ∧
      detUnion ≤
        detA * detB *
          Real.exp (2 * ((Fintype.card α : ℝ) * (Fintype.card β : ℝ)) *
            Real.log rhoMin) := by
  classical
  have hterm :
      ∀ a b, -Real.log rhoMin ≤ -Real.log (rho a b) := by
    intro a b
    exact neg_le_neg (Real.log_le_log (hrho_pos a b) (hrho_le_min a b))
  let C : ℝ := -Real.log rhoMin
  have hsum_const :
      (∑ a : α, ∑ b : β, C) =
        ((Fintype.card α : ℝ) * (Fintype.card β : ℝ)) * C := by
    simp [C, Finset.sum_const, nsmul_eq_mul, mul_assoc]
  have hsum_lower :
      ((Fintype.card α : ℝ) * (Fintype.card β : ℝ)) * (-Real.log rhoMin) ≤
        ∑ a, ∑ b, -Real.log (rho a b) := by
    calc
      ((Fintype.card α : ℝ) * (Fintype.card β : ℝ)) * (-Real.log rhoMin) =
          ∑ a : α, ∑ b : β, C := by
            simpa [C] using hsum_const.symm
      _ ≤ ∑ a, ∑ b, -Real.log (rho a b) := by
            refine Finset.sum_le_sum ?_
            intro a _
            exact Finset.sum_le_sum fun b _ => by simpa [C] using hterm a b
  have henergy_lower :
      2 * ((Fintype.card α : ℝ) * (Fintype.card β : ℝ)) * (-Real.log rhoMin) ≤
        crossEnergy := by
    calc
      2 * ((Fintype.card α : ℝ) * (Fintype.card β : ℝ)) * (-Real.log rhoMin) =
          2 * (((Fintype.card α : ℝ) * (Fintype.card β : ℝ)) *
            (-Real.log rhoMin)) := by
            ring
      _ ≤ 2 * (∑ a, ∑ b, -Real.log (rho a b)) :=
            mul_le_mul_of_nonneg_left hsum_lower (by norm_num)
      _ = crossEnergy := by
            rw [hcross]
  have hexp_le :
      Real.exp (-crossEnergy) ≤
        Real.exp (2 * ((Fintype.card α : ℝ) * (Fintype.card β : ℝ)) *
          Real.log rhoMin) := by
    refine Real.exp_le_exp.mpr ?_
    have hneg :
        -crossEnergy ≤
          -(2 * ((Fintype.card α : ℝ) * (Fintype.card β : ℝ)) *
            (-Real.log rhoMin)) := by
      linarith
    have hrewrite :
        -(2 * ((Fintype.card α : ℝ) * (Fintype.card β : ℝ)) *
            (-Real.log rhoMin)) =
          2 * ((Fintype.card α : ℝ) * (Fintype.card β : ℝ)) *
            Real.log rhoMin := by
      ring
    rwa [hrewrite] at hneg
  constructor
  · exact henergy_lower
  · calc
      detUnion = detA * detB * Real.exp (-crossEnergy) := hdet
      _ ≤
          detA * detB *
            Real.exp (2 * ((Fintype.card α : ℝ) * (Fintype.card β : ℝ)) *
              Real.log rhoMin) :=
            mul_le_mul_of_nonneg_left hexp_le hdetProd_nonneg

end Omega.Zeta
