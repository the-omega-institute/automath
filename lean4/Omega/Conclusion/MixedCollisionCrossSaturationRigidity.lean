import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators InnerProductSpace

/-- Paper label: `cor:conclusion-mixed-collision-cross-saturation-rigidity`. -/
theorem paper_conclusion_mixed_collision_cross_saturation_rigidity {X : Type} [Fintype X]
    (q : ℕ) (hq : 1 ≤ q) (w0 w1 : X → ℝ) (hw0 : ∀ x, 0 ≤ w0 x)
    (hw1 : ∀ x, 0 ≤ w1 x) (hmass0 : ∑ x, w0 x ^ q = 1)
    (hmass1 : ∑ x, w1 x ^ q = 1) :
    (∑ x, (w0 x * w1 x) ^ q) ^ 2 ≤
        (∑ x, w0 x ^ (2 * q)) * (∑ x, w1 x ^ (2 * q)) ∧
      (((∑ x, (w0 x * w1 x) ^ q) ^ 2 =
          (∑ x, w0 x ^ (2 * q)) * (∑ x, w1 x ^ (2 * q))) ↔
        ∀ x, w0 x = w1 x) := by
  classical
  let a : EuclideanSpace ℝ X := WithLp.toLp 2 fun x => w0 x ^ q
  let b : EuclideanSpace ℝ X := WithLp.toLp 2 fun x => w1 x ^ q
  have hq0 : q ≠ 0 := by omega
  have ha_nonneg : ∀ x, 0 ≤ a x := fun x => pow_nonneg (hw0 x) q
  have hb_nonneg : ∀ x, 0 ≤ b x := fun x => pow_nonneg (hw1 x) q
  have hmassa : ∑ x, a x = 1 := by simpa [a] using hmass0
  have hmassb : ∑ x, b x = 1 := by simpa [b] using hmass1
  have hinner_sum : ⟪a, b⟫_ℝ = ∑ x, (w0 x * w1 x) ^ q := by
    simp [a, b, PiLp.inner_apply, mul_pow, mul_comm]
  have hnorma_mul : ‖a‖ * ‖a‖ = ∑ x, w0 x ^ (2 * q) := by
    have hsq := EuclideanSpace.norm_sq_eq (𝕜 := ℝ) (n := X) a
    rw [pow_two] at hsq
    rw [hsq]
    apply Finset.sum_congr rfl
    intro x _
    simp [a, Real.norm_eq_abs, abs_of_nonneg (hw0 x), pow_mul, mul_comm]
  have hnormb_mul : ‖b‖ * ‖b‖ = ∑ x, w1 x ^ (2 * q) := by
    have hsq := EuclideanSpace.norm_sq_eq (𝕜 := ℝ) (n := X) b
    rw [pow_two] at hsq
    rw [hsq]
    apply Finset.sum_congr rfl
    intro x _
    simp [b, Real.norm_eq_abs, abs_of_nonneg (hw1 x), pow_mul, mul_comm]
  have hineq_inner := real_inner_mul_inner_self_le a b
  refine ⟨?_, ?_⟩
  · simpa [hinner_sum, hnorma_mul, hnormb_mul, pow_two, mul_assoc] using hineq_inner
  · constructor
    · intro hsat
      have hsq :
          ⟪a, b⟫_ℝ ^ 2 = (‖a‖ * ‖b‖) ^ 2 := by
        have hsat_inner :
            ⟪a, b⟫_ℝ ^ 2 = (‖a‖ * ‖a‖) * (‖b‖ * ‖b‖) := by
          simpa [hinner_sum, hnorma_mul, hnormb_mul, pow_two] using hsat
        rw [hsat_inner]
        ring
      have hinner_nonneg : 0 ≤ ⟪a, b⟫_ℝ := by
        rw [hinner_sum]
        exact Finset.sum_nonneg fun x _ => pow_nonneg (mul_nonneg (hw0 x) (hw1 x)) q
      have hnorm_mul_nonneg : 0 ≤ ‖a‖ * ‖b‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
      have hinner_eq_norm : ⟪a, b⟫_ℝ = ‖a‖ * ‖b‖ := by
        have habs := (sq_eq_sq_iff_abs_eq_abs (⟪a, b⟫_ℝ) (‖a‖ * ‖b‖)).mp hsq
        simpa [abs_of_nonneg hinner_nonneg, abs_of_nonneg hnorm_mul_nonneg] using habs
      have hscaled : ‖b‖ • a = ‖a‖ • b :=
        (inner_eq_norm_mul_iff_real (x := a) (y := b)).mp hinner_eq_norm
      have hnorm_eq : ‖b‖ = ‖a‖ := by
        have hsum := congr_arg (fun f : EuclideanSpace ℝ X => ∑ x, f x) hscaled
        simp only [PiLp.smul_apply, smul_eq_mul] at hsum
        rw [← Finset.mul_sum, ← Finset.mul_sum, hmassa, hmassb, mul_one, mul_one] at hsum
        exact hsum
      have ha_ne : a ≠ 0 := by
        intro ha0
        have : (∑ x, a x) = 0 := by simp [ha0]
        linarith
      have hnorma_ne : ‖a‖ ≠ 0 := by simpa using (norm_ne_zero_iff.mpr ha_ne)
      have hab : a = b := by
        ext x
        have hx := congr_arg (fun f : EuclideanSpace ℝ X => f x) hscaled
        rw [hnorm_eq] at hx
        simpa using mul_left_cancel₀ hnorma_ne hx
      intro x
      have hpow : w0 x ^ q = w1 x ^ q := congr_arg (fun f : EuclideanSpace ℝ X => f x) hab
      exact (pow_left_inj₀ (hw0 x) (hw1 x) hq0).mp hpow
    · intro hw
      have hcross :
          (∑ x, (w0 x * w1 x) ^ q) = ∑ x, w0 x ^ (2 * q) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [hw x, mul_pow, ← pow_add]
        congr 1
        omega
      rw [hcross]
      have hsame :
          (∑ x, w1 x ^ (2 * q)) = ∑ x, w0 x ^ (2 * q) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [← hw x]
      rw [hsame]
      ring

end Omega.Conclusion
