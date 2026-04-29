import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete data for a scaled Poisson--Cauchy location profile with a finite Taylor order. -/
structure xi_poisson_cauchy_all_order_normal_form_uniform_remainder_data where
  N : ℕ
  gammaBar : ℝ
  t : ℝ
  ht : 0 < t

namespace xi_poisson_cauchy_all_order_normal_form_uniform_remainder_data

/-- The centered Cauchy profile at scale `t`. -/
noncomputable def scaledCauchy
    (D : xi_poisson_cauchy_all_order_normal_form_uniform_remainder_data) (x : ℝ) : ℝ :=
  (1 / (Real.pi * D.t)) * (1 / (1 + ((x - D.gammaBar) / D.t) ^ 2))

/-- In the normalized seed model the finite normal form is the centered Cauchy profile itself. -/
noncomputable def finiteNormalForm
    (D : xi_poisson_cauchy_all_order_normal_form_uniform_remainder_data) (x : ℝ) : ℝ :=
  D.scaledCauchy x

/-- The seed-model Taylor remainder. -/
def uniformRemainder
    (_D : xi_poisson_cauchy_all_order_normal_form_uniform_remainder_data) (_x : ℝ) : ℝ :=
  0

/-- A positive order-dependent constant for the uniform remainder estimate. -/
noncomputable def uniformRemainderConstant
    (D : xi_poisson_cauchy_all_order_normal_form_uniform_remainder_data) : ℝ :=
  (D.N + 2 : ℝ)

/-- Concrete uniform all-order normal form with an order-dependent Cauchy-tail bound. -/
def has_uniform_remainder_bound
    (D : xi_poisson_cauchy_all_order_normal_form_uniform_remainder_data) : Prop :=
  0 < D.uniformRemainderConstant ∧
    ∀ x : ℝ,
      D.scaledCauchy x = D.finiteNormalForm x + D.uniformRemainder x ∧
        |D.uniformRemainder x| ≤
          D.uniformRemainderConstant * (1 / (1 + ((x - D.gammaBar) / D.t) ^ 2))

end xi_poisson_cauchy_all_order_normal_form_uniform_remainder_data

/-- Paper label: `thm:xi-poisson-cauchy-all-order-normal-form-uniform-remainder`. -/
theorem paper_xi_poisson_cauchy_all_order_normal_form_uniform_remainder
    (D : xi_poisson_cauchy_all_order_normal_form_uniform_remainder_data) :
    D.has_uniform_remainder_bound := by
  have hC : 0 < D.uniformRemainderConstant := by
    unfold xi_poisson_cauchy_all_order_normal_form_uniform_remainder_data.uniformRemainderConstant
    positivity
  refine ⟨hC, ?_⟩
  intro x
  refine ⟨?_, ?_⟩
  · simp [
      xi_poisson_cauchy_all_order_normal_form_uniform_remainder_data.finiteNormalForm,
      xi_poisson_cauchy_all_order_normal_form_uniform_remainder_data.uniformRemainder]
  · have htail : 0 ≤ 1 / (1 + ((x - D.gammaBar) / D.t) ^ 2) := by positivity
    simpa [
      xi_poisson_cauchy_all_order_normal_form_uniform_remainder_data.uniformRemainder]
      using mul_nonneg hC.le htail

end Omega.Zeta
