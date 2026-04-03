import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Two-atom scalar for general real parameter `α`.
    def:conclusion-binfold-single-scalar-recovers-golden-parameter -/
noncomputable def twoAtomScalar (α φ : ℝ) : ℝ :=
  5 ^ (-α / 2) * (φ ^ (2 * α - 1) + φ ^ (α - 2)) - 1

noncomputable def twoAtomScalar2 (φ : ℝ) : ℝ := (φ ^ 3 + 1) / 5 - 1

/-- α = 2 specialization of the two-atom scalar.
    cor:conclusion-binfold-single-scalar-recovers-golden-parameter -/
theorem twoAtomScalar2_goldenRatio :
    twoAtomScalar2 Real.goldenRatio = (Real.goldenRatio ^ 3 + 1) / 5 - 1 := rfl

/-- Strict monotonicity on the positive reals.
    cor:conclusion-binfold-single-scalar-recovers-golden-parameter -/
theorem twoAtomScalar2_strictMono {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    twoAtomScalar2 x < twoAtomScalar2 y := by
  unfold twoAtomScalar2
  have hy : 0 < y := lt_trans hx hxy
  have hfac : 0 < x ^ 2 + x * y + y ^ 2 := by positivity
  have hpow : x ^ 3 < y ^ 3 := by
    have : 0 < y ^ 3 - x ^ 3 := by
      rw [show y ^ 3 - x ^ 3 = (y - x) * (x ^ 2 + x * y + y ^ 2) by ring]
      exact mul_pos (sub_pos.mpr hxy) hfac
    linarith
  linarith

/-- Injectivity of the α = 2 scalar on the positive reals.
    cor:conclusion-binfold-single-scalar-recovers-golden-parameter -/
theorem twoAtomScalar2_injective_on_pos :
    Set.InjOn twoAtomScalar2 {φ : ℝ | 0 < φ} := by
  intro x hx y hy hEq
  by_cases hxy : x < y
  · have hstrict := twoAtomScalar2_strictMono hx hxy
    rw [hEq] at hstrict
    exact (lt_irrefl _ hstrict).elim
  · by_cases hyx : y < x
    · have hstrict := twoAtomScalar2_strictMono hy hyx
      rw [hEq] at hstrict
      exact (lt_irrefl _ hstrict).elim
    · linarith

/-- Strict monotonicity of the two-atom scalar on `(1, ∞)`.
    cor:conclusion-binfold-single-scalar-recovers-golden-parameter -/
theorem twoAtomScalar_strictMono {α : ℝ} (hα : 1 < α) :
    StrictMonoOn (twoAtomScalar α) (Set.Ioi 1) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioi 1) ?_ ?_
  · refine continuousOn_of_forall_continuousAt ?_
    intro x hx
    have hx_pos : 0 < x := lt_trans zero_lt_one hx
    unfold twoAtomScalar
    refine (continuousAt_const.mul ?_).sub (continuousAt_const : ContinuousAt (fun _ : ℝ => (1 : ℝ)) x)
    exact (Real.continuousAt_rpow_const x (2 * α - 1) (Or.inl hx_pos.ne')).add
      (Real.continuousAt_rpow_const x (α - 2) (Or.inl hx_pos.ne'))
  · intro φ hφ
    have hφ' : 1 < φ := by simpa [interior_Ioi, Set.mem_Ioi] using hφ
    have hφ_pos : 0 < φ := lt_trans zero_lt_one hφ'

    have hfive_pos : 0 < (5 : ℝ) := by norm_num
    have hpow5_pos : 0 < ((5 : ℝ) ^ (-α / 2 : ℝ)) := Real.rpow_pos_of_pos hfive_pos _
    have hφa1_pos : 0 < φ ^ (α - 3) := Real.rpow_pos_of_pos hφ_pos _
    have hφap1_gt_one : 1 < φ ^ (α + 1) := by
      apply Real.one_lt_rpow hφ'
      linarith
    have hmain_gt : 0 < (2 * α - 1) * φ ^ (α + 1) + (α - 2) := by
      have hcoeff_pos : 0 < 2 * α - 1 := by linarith
      have hcoeff_mul_gt : 2 * α - 1 < (2 * α - 1) * φ ^ (α + 1) := by
        simpa using (mul_lt_mul_of_pos_left hφap1_gt_one hcoeff_pos)
      have hlower : 3 * α - 3 < (2 * α - 1) * φ ^ (α + 1) + (α - 2) := by
        linarith
      linarith
    have hderiv :
        deriv (twoAtomScalar α) φ =
          ((5 : ℝ) ^ (-α / 2 : ℝ)) * φ ^ (α - 3) * ((2 * α - 1) * φ ^ (α + 1) + (α - 2)) := by
      unfold twoAtomScalar
      rw [deriv_sub_const]
      rw [deriv_const_mul_field]
      rw [show deriv (fun φ : ℝ => φ ^ (2 * α - 1) + φ ^ (α - 2)) φ =
            deriv (fun x : ℝ => x ^ (2 * α - 1)) φ + deriv (fun x : ℝ => x ^ (α - 2)) φ by
            exact deriv_add
              (Real.hasDerivAt_rpow_const (x := φ) (p := 2 * α - 1)
                (Or.inr (show 1 ≤ 2 * α - 1 by linarith))).differentiableAt
              (Real.hasDerivAt_rpow_const (x := φ) (p := α - 2)
                (Or.inl hφ_pos.ne')).differentiableAt]
      rw [Real.deriv_rpow_const, Real.deriv_rpow_const]
      have hpow_eq : φ ^ (2 * α - 1 - 1) = φ ^ (α - 3) * φ ^ (α + 1) := by
        have : 2 * α - 1 - 1 = (α - 3) + (α + 1) := by ring
        rw [this, Real.rpow_add hφ_pos]
      rw [hpow_eq]
      ring_nf
    rw [hderiv]
    exact mul_pos (mul_pos hpow5_pos hφa1_pos) hmain_gt

/-- Injectivity of the two-atom scalar on `(1, ∞)`.
    cor:conclusion-binfold-single-scalar-recovers-golden-parameter -/
theorem twoAtomScalar_injective_on_Ioi {α : ℝ} (hα : 1 < α) :
    Set.InjOn (twoAtomScalar α) (Set.Ioi 1) :=
  (twoAtomScalar_strictMono hα).injOn

/-- The α = 2 scalar recovers the golden ratio from its value on `(1, ∞)`.
    cor:conclusion-binfold-single-scalar-recovers-golden-parameter -/
theorem twoAtomScalar2_eq_zero_iff_goldenRatio {φ : ℝ} (hφ : 1 < φ) :
    twoAtomScalar2 φ = twoAtomScalar2 Real.goldenRatio ↔ φ = Real.goldenRatio := by
  have hgr : 1 < Real.goldenRatio := Real.one_lt_goldenRatio
  have hφpos : 0 < φ := lt_trans zero_lt_one hφ
  have hgrpos : 0 < Real.goldenRatio := lt_trans zero_lt_one hgr
  constructor
  · intro h
    exact twoAtomScalar2_injective_on_pos hφpos hgrpos h
  · intro h
    rw [h]

end Omega.Conclusion
