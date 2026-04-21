import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

namespace Omega.OperatorAlgebra

/-- The zero event attached to a fixed joint-spectral pair `(lam, theta)` on the critical line. -/
def hzomZeroAt (lam theta t : ℝ) : Prop :=
  Real.sin (lam * t - theta) = 0 ∧ Real.cos (lam * t - theta) = 1

/-- Paper label: `cor:op-algebra-hzom-critical-zeros-joint-spectrum-comb`. The critical zero
heights attached to a fixed joint-spectral point `(lam, θ)` form the arithmetic comb
`((θ + 2πk) / lam)_{k ∈ ℤ}`. -/
theorem paper_op_algebra_hzom_critical_zeros_joint_spectrum_comb (lam theta : ℝ) (hlam : 0 < lam) :
    (∀ k : ℤ, hzomZeroAt lam theta ((theta + 2 * Real.pi * (k : ℝ)) / lam)) ∧
      (∀ t : ℝ, hzomZeroAt lam theta t → ∃ k : ℤ, t = (theta + 2 * Real.pi * (k : ℝ)) / lam) := by
  have hlam0 : lam ≠ 0 := ne_of_gt hlam
  refine ⟨?_, ?_⟩
  · intro k
    unfold hzomZeroAt
    constructor
    · have hdiv : lam * ((theta + 2 * Real.pi * (k : ℝ)) / lam) = theta + 2 * Real.pi * (k : ℝ) := by
        field_simp [hlam0]
      calc
        Real.sin (lam * ((theta + 2 * Real.pi * (k : ℝ)) / lam) - theta)
            = Real.sin ((theta + 2 * Real.pi * (k : ℝ)) - theta) := by rw [hdiv]
        _ = Real.sin (2 * Real.pi * (k : ℝ)) := by ring_nf
        _ = 0 := by
            simpa [mul_comm, mul_left_comm, mul_assoc] using (Real.sin_add_int_mul_two_pi 0 k)
    · have hdiv : lam * ((theta + 2 * Real.pi * (k : ℝ)) / lam) = theta + 2 * Real.pi * (k : ℝ) := by
        field_simp [hlam0]
      calc
        Real.cos (lam * ((theta + 2 * Real.pi * (k : ℝ)) / lam) - theta)
            = Real.cos ((theta + 2 * Real.pi * (k : ℝ)) - theta) := by rw [hdiv]
        _ = Real.cos (2 * Real.pi * (k : ℝ)) := by ring_nf
        _ = 1 := by simpa [mul_comm, mul_left_comm, mul_assoc] using Real.cos_int_mul_two_pi k
  · intro t ht
    rcases (Real.cos_eq_one_iff _).1 ht.2 with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [eq_div_iff hlam0]
    nlinarith [hk]

end Omega.OperatorAlgebra
