import Mathlib.Tactic

namespace Omega.Zeta

/-- Field elements generated from the finite local scalar seeds by the rational field operations. -/
inductive xi_time_part9zbha_finite_local_algebra_even_zeta_factorization_generated
    {K : Type*} [Field K] (seed : K → Prop) : K → Prop
  | seed {x : K} (hx : seed x) :
      xi_time_part9zbha_finite_local_algebra_even_zeta_factorization_generated seed x
  | zero :
      xi_time_part9zbha_finite_local_algebra_even_zeta_factorization_generated seed 0
  | one :
      xi_time_part9zbha_finite_local_algebra_even_zeta_factorization_generated seed 1
  | add {x y : K}
      (hx : xi_time_part9zbha_finite_local_algebra_even_zeta_factorization_generated seed x)
      (hy : xi_time_part9zbha_finite_local_algebra_even_zeta_factorization_generated seed y) :
      xi_time_part9zbha_finite_local_algebra_even_zeta_factorization_generated seed (x + y)
  | neg {x : K}
      (hx : xi_time_part9zbha_finite_local_algebra_even_zeta_factorization_generated seed x) :
      xi_time_part9zbha_finite_local_algebra_even_zeta_factorization_generated seed (-x)
  | mul {x y : K}
      (hx : xi_time_part9zbha_finite_local_algebra_even_zeta_factorization_generated seed x)
      (hy : xi_time_part9zbha_finite_local_algebra_even_zeta_factorization_generated seed y) :
      xi_time_part9zbha_finite_local_algebra_even_zeta_factorization_generated seed (x * y)
  | inv {x : K}
      (hx : xi_time_part9zbha_finite_local_algebra_even_zeta_factorization_generated seed x) :
      xi_time_part9zbha_finite_local_algebra_even_zeta_factorization_generated seed x⁻¹

/-- Paper label: `thm:xi-time-part9zbha-finite-local-algebra-even-zeta-factorization`. -/
theorem paper_xi_time_part9zbha_finite_local_algebra_even_zeta_factorization
    {K : Type*} [Field K] (seed : K → Prop) (evenZetaField : Subfield K)
    (hSeed : ∀ x, seed x → x ∈ evenZetaField) :
    ∀ x,
      xi_time_part9zbha_finite_local_algebra_even_zeta_factorization_generated seed x →
        x ∈ evenZetaField := by
  intro x hx
  induction hx with
  | seed hx =>
      exact hSeed _ hx
  | zero =>
      exact evenZetaField.zero_mem
  | one =>
      exact evenZetaField.one_mem
  | add _ _ hx_mem hy_mem =>
      exact evenZetaField.add_mem hx_mem hy_mem
  | neg _ hx_mem =>
      exact evenZetaField.neg_mem hx_mem
  | mul _ _ hx_mem hy_mem =>
      exact evenZetaField.mul_mem hx_mem hy_mem
  | inv _ hx_mem =>
      exact evenZetaField.inv_mem hx_mem

end Omega.Zeta
