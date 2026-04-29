import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Paper label: `prop:xi-delta-flow-moment-ladder-commutation`. -/
theorem paper_xi_delta_flow_moment_ladder_commutation {ι : Type*} [Fintype ι] (a w : ι → ℝ)
    (z Δ : ℝ) (k : ℕ)
    (hden : ∀ i, 1 - z * Real.exp (-(Δ * a i)) ≠ 0) :
    HasDerivAt
      (fun Δ' => ∑ i, w i * a i ^ k / (1 - z * Real.exp (-(Δ' * a i))))
      (-z *
        deriv
          (fun z' => ∑ i, w i * a i ^ (k + 1) / (1 - z' * Real.exp (-(Δ * a i))))
          z)
      Δ := by
  have hzDeriv :
      HasDerivAt
        (fun z' => ∑ i, w i * a i ^ (k + 1) / (1 - z' * Real.exp (-(Δ * a i))))
        (∑ i,
          w i * a i ^ (k + 1) * Real.exp (-(Δ * a i)) /
            (1 - z * Real.exp (-(Δ * a i))) ^ 2)
        z := by
    refine HasDerivAt.fun_sum fun i _ => ?_
    have hdenom :
        HasDerivAt (fun z' : ℝ => 1 - z' * Real.exp (-(Δ * a i)))
          (-Real.exp (-(Δ * a i))) z := by
      simpa [sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using
        (((hasDerivAt_id z).mul_const (Real.exp (-(Δ * a i)))).neg.const_add (1 : ℝ))
    have hinv :
        HasDerivAt (fun z' : ℝ => (1 - z' * Real.exp (-(Δ * a i)))⁻¹)
          (Real.exp (-(Δ * a i)) / (1 - z * Real.exp (-(Δ * a i))) ^ 2) z := by
      convert hdenom.inv (hden i) using 1
      ring
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      hinv.const_mul (w i * a i ^ (k + 1))
  have hΔDeriv :
      HasDerivAt
        (fun Δ' => ∑ i, w i * a i ^ k / (1 - z * Real.exp (-(Δ' * a i))))
        (∑ i,
          -(z * (w i * a i ^ (k + 1) * Real.exp (-(Δ * a i)) /
            (1 - z * Real.exp (-(Δ * a i))) ^ 2)))
        Δ := by
    refine HasDerivAt.fun_sum fun i _ => ?_
    have harg : HasDerivAt (fun Δ' : ℝ => -(Δ' * a i)) (-(a i)) Δ := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        ((hasDerivAt_id Δ).mul_const (a i)).neg
    have hexp :
        HasDerivAt (fun Δ' : ℝ => Real.exp (-(Δ' * a i)))
          (-(a i) * Real.exp (-(Δ * a i))) Δ := by
      simpa [Function.comp_def, mul_comm, mul_left_comm, mul_assoc] using
        (Real.hasDerivAt_exp (-(Δ * a i))).comp Δ harg
    have hdenom :
        HasDerivAt (fun Δ' : ℝ => 1 - z * Real.exp (-(Δ' * a i)))
          (z * a i * Real.exp (-(Δ * a i))) Δ := by
      simpa [sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using
        (hexp.const_mul z).neg.const_add (1 : ℝ)
    have hinv :
        HasDerivAt (fun Δ' : ℝ => (1 - z * Real.exp (-(Δ' * a i)))⁻¹)
          (-(z * a i * Real.exp (-(Δ * a i)) /
            (1 - z * Real.exp (-(Δ * a i))) ^ 2)) Δ := by
      convert hdenom.inv (hden i) using 1
      ring
    simpa [div_eq_mul_inv, pow_succ, mul_comm, mul_left_comm, mul_assoc] using
      hinv.const_mul (w i * a i ^ k)
  rw [hzDeriv.deriv]
  simpa [Finset.mul_sum, pow_succ, mul_comm, mul_left_comm, mul_assoc] using hΔDeriv

end Omega.Zeta
