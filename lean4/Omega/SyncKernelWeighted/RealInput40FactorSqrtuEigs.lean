import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

noncomputable section

/-- The explicit linear factor pair induced by the atomic term `1 - u z^2`. -/
def realInput40SqrtuFactor (u : ℝ) (z : ℂ) : ℂ :=
  (1 - z * Complex.ofReal (Real.sqrt u)) * (1 + z * Complex.ofReal (Real.sqrt u))

/-- The trace contribution of the two rigid branches `±sqrt(u)`. -/
def realInput40SqrtuTraceContribution (u : ℝ) (n : ℕ) : ℂ :=
  Complex.ofReal (Real.sqrt u) ^ n + (-Complex.ofReal (Real.sqrt u)) ^ n

lemma realInput40_sqrtu_factor_eq (u : ℝ) (hu : 0 ≤ u) (z : ℂ) :
    realInput40SqrtuFactor u z = 1 - (u : ℂ) * z ^ 2 := by
  let a : ℂ := Complex.ofReal (Real.sqrt u)
  have hsq : a ^ 2 = (u : ℂ) := by
    simpa [a] using (show ((Real.sqrt u : ℂ) ^ 2 = (u : ℂ)) from by
      exact_mod_cast Real.sq_sqrt hu)
  unfold realInput40SqrtuFactor
  calc
    (1 - z * a) * (1 + z * a) = 1 - (z * a) ^ 2 := by ring
    _ = 1 - z ^ 2 * a ^ 2 := by ring
    _ = 1 - (u : ℂ) * z ^ 2 := by rw [hsq]; ring

lemma realInput40_sqrtu_trace_even (u : ℝ) (hu : 0 ≤ u) (k : ℕ) :
    realInput40SqrtuTraceContribution u (2 * k) = 2 * (u : ℂ) ^ k := by
  let a : ℂ := Complex.ofReal (Real.sqrt u)
  have hsq : a ^ 2 = (u : ℂ) := by
    simpa [a] using (show ((Real.sqrt u : ℂ) ^ 2 = (u : ℂ)) from by
      exact_mod_cast Real.sq_sqrt hu)
  unfold realInput40SqrtuTraceContribution
  calc
    a ^ (2 * k) + (-a) ^ (2 * k) = (a ^ 2) ^ k + ((-a) ^ 2) ^ k := by
      rw [pow_mul, pow_mul]
    _ = (u : ℂ) ^ k + (u : ℂ) ^ k := by simp [hsq]
    _ = 2 * (u : ℂ) ^ k := by ring

lemma realInput40_sqrtu_trace_odd (u : ℝ) (k : ℕ) :
    realInput40SqrtuTraceContribution u (2 * k + 1) = 0 := by
  let a : ℂ := Complex.ofReal (Real.sqrt u)
  have hEvenPow : (-a) ^ (2 * k) = a ^ (2 * k) := by
    rw [pow_mul, pow_mul]
    simp
  unfold realInput40SqrtuTraceContribution
  calc
    a ^ (2 * k + 1) + (-a) ^ (2 * k + 1)
        = a ^ (2 * k) * a + (-a) ^ (2 * k) * (-a) := by simp [pow_succ']
    _ = a ^ (2 * k) * a + a ^ (2 * k) * (-a) := by rw [hEvenPow]
    _ = 0 := by ring

/-- Split `1 - u z^2` into the rigid linear factors `1 ∓ z sqrt(u)` and read off the exact
parity-dependent trace contribution of the two explicit branches `±sqrt(u)`.
    cor:real-input-40-factor-sqrtu-eigs -/
theorem paper_real_input_40_factor_sqrtu_eigs (u : ℝ) (hu : 0 ≤ u) (z : ℂ) (n : ℕ) :
    realInput40SqrtuFactor u z = 1 - (u : ℂ) * z ^ 2 ∧
      realInput40SqrtuTraceContribution u n =
        if Even n then 2 * (u : ℂ) ^ (n / 2) else 0 := by
  refine ⟨realInput40_sqrtu_factor_eq u hu z, ?_⟩
  by_cases hEven : Even n
  · rcases hEven with ⟨k, rfl⟩
    rw [if_pos ⟨k, rfl⟩]
    have hdiv : (k + k) / 2 = k := by omega
    rw [hdiv]
    simpa [two_mul] using realInput40_sqrtu_trace_even u hu k
  · rcases Nat.not_even_iff_odd.mp hEven with ⟨k, rfl⟩
    simp [realInput40_sqrtu_trace_odd]

end

end Omega.SyncKernelWeighted
