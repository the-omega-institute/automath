import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

theorem paper_pom_reverse_kl_bound_by_dispersion {X : Type} [Fintype X] [DecidableEq X] [Nonempty X]
    (w : X → ℝ) (hw_pos : ∀ x, 0 < w x) (_hw_sum : (∑ x, w x) = 1) :
    (∑ x, (Fintype.card X : ℝ)⁻¹ * Real.log (((Fintype.card X : ℝ)⁻¹) / w x)) ≤
      Real.log ((((Fintype.card X : ℝ)⁻¹)^2) * ∑ x, (w x)⁻¹) := by
  let n : ℝ := Fintype.card X
  have hn_nat : 0 < Fintype.card X := Fintype.card_pos_iff.mpr inferInstance
  have hn_pos : 0 < n := by
    simpa [n] using (show (0 : ℝ) < (Fintype.card X : ℝ) by exact_mod_cast hn_nat)
  have hn_ne : n ≠ 0 := ne_of_gt hn_pos
  have hn_inv_pos : 0 < n⁻¹ := inv_pos.mpr hn_pos
  have hweights_nonneg : ∀ x ∈ (Finset.univ : Finset X), 0 ≤ n⁻¹ := by
    intro x hx
    exact hn_inv_pos.le
  have hweights_sum : ∑ x ∈ (Finset.univ : Finset X), n⁻¹ = 1 := by
    simp [n, hn_ne]
  have hmem : ∀ x ∈ (Finset.univ : Finset X), (w x)⁻¹ ∈ Set.Ioi (0 : ℝ) := by
    intro x hx
    exact inv_pos.mpr (hw_pos x)
  have hJensen :=
    (strictConcaveOn_log_Ioi.concaveOn).le_map_sum (t := (Finset.univ : Finset X))
      (w := fun _ => n⁻¹) (p := fun x => (w x)⁻¹) hweights_nonneg hweights_sum hmem
  have hlog_avg :
      ∑ x, n⁻¹ * Real.log ((w x)⁻¹) ≤ Real.log (∑ x, n⁻¹ * (w x)⁻¹) := by
    simpa [smul_eq_mul] using hJensen
  have havg_inv_pos : 0 < ∑ x, n⁻¹ * (w x)⁻¹ := by
    classical
    rcases ‹Nonempty X› with ⟨x0⟩
    have hx0_pos : 0 < n⁻¹ * (w x0)⁻¹ := by
      exact mul_pos hn_inv_pos (inv_pos.mpr (hw_pos x0))
    have hle :
        n⁻¹ * (w x0)⁻¹ ≤ ∑ x, n⁻¹ * (w x)⁻¹ := by
      exact Finset.single_le_sum
        (fun x hx => mul_nonneg hn_inv_pos.le (inv_nonneg.mpr (hw_pos x).le))
        (by simp : x0 ∈ (Finset.univ : Finset X))
    exact lt_of_lt_of_le hx0_pos hle
  have hweights_sum' : ∑ x : X, n⁻¹ = 1 := by
    simpa using hweights_sum
  have hleft :
      (∑ x, n⁻¹ * Real.log (n⁻¹ / w x)) =
        Real.log n⁻¹ + ∑ x, n⁻¹ * Real.log ((w x)⁻¹) := by
    calc
      (∑ x, n⁻¹ * Real.log (n⁻¹ / w x)) =
          ∑ x, n⁻¹ * (Real.log n⁻¹ + Real.log ((w x)⁻¹)) := by
            refine Finset.sum_congr rfl ?_
            intro x hx
            rw [div_eq_mul_inv, Real.log_mul (inv_ne_zero hn_ne) (inv_ne_zero (hw_pos x).ne')]
      _ = ∑ x, (n⁻¹ * Real.log n⁻¹ + n⁻¹ * Real.log ((w x)⁻¹)) := by
            refine Finset.sum_congr rfl ?_
            intro x hx
            ring
      _ = (∑ x, n⁻¹ * Real.log n⁻¹) + ∑ x, n⁻¹ * Real.log ((w x)⁻¹) := by
            rw [Finset.sum_add_distrib]
      _ = (∑ x, n⁻¹) * Real.log n⁻¹ + ∑ x, n⁻¹ * Real.log ((w x)⁻¹) := by
            rw [Finset.sum_mul]
      _ = Real.log n⁻¹ + ∑ x, n⁻¹ * Real.log ((w x)⁻¹) := by
            rw [hweights_sum']
            ring
  have hright :
      Real.log ((n⁻¹)^2 * ∑ x, (w x)⁻¹) = Real.log n⁻¹ + Real.log (∑ x, n⁻¹ * (w x)⁻¹) := by
    calc
      Real.log ((n⁻¹)^2 * ∑ x, (w x)⁻¹) =
          Real.log (n⁻¹ * (∑ x, n⁻¹ * (w x)⁻¹)) := by
            congr 1
            rw [show (∑ x, n⁻¹ * (w x)⁻¹) = n⁻¹ * ∑ x, (w x)⁻¹ by rw [Finset.mul_sum]]
            ring
      _ = Real.log n⁻¹ + Real.log (∑ x, n⁻¹ * (w x)⁻¹) := by
            rw [Real.log_mul (inv_ne_zero hn_ne) (ne_of_gt havg_inv_pos)]
  calc
    (∑ x, (Fintype.card X : ℝ)⁻¹ * Real.log (((Fintype.card X : ℝ)⁻¹) / w x)) =
        Real.log n⁻¹ + ∑ x, n⁻¹ * Real.log ((w x)⁻¹) := by
          simpa [n] using hleft
    _ ≤ Real.log n⁻¹ + Real.log (∑ x, n⁻¹ * (w x)⁻¹) := by
          simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right hlog_avg (Real.log n⁻¹)
    _ = Real.log ((((Fintype.card X : ℝ)⁻¹)^2) * ∑ x, (w x)⁻¹) := by
          simpa [n] using hright.symm

end Omega.POM
