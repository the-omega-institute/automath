import Mathlib
import Omega.Zeta.AdamsFiberMobiusInversion

open scoped ArithmeticFunction.Moebius BigOperators

namespace Omega.Zeta

/-- Concrete finite-`N` Adams-fiber Möbius inversion error package on a fixed odd fiber. -/
structure xi_adams_fiber_mobius_inversion_finiten_error_data where
  m : ℕ → ℤ
  f : ℕ → ℤ
  mhat : ℕ → ℤ
  a : ℕ
  u : ℕ
  endpointError : ℕ → ℝ
  spectralGapTerm : ℕ → ℝ
  hu_pos : 0 < u
  hu_odd : Odd u
  endpointDecomposition :
    ∀ v > 0, Odd v →
      Finset.sum (oddDivisors v) (fun w => adamsExactOrderMass f a w) = adamsEndpointProbeMass m a v
  term_error_bound :
    ∀ x ∈ u.divisorsAntidiagonal,
      |((((μ x.1 : ℤ) * adamsEndpointProbeMass mhat a x.2) -
          ((μ x.1 : ℤ) * adamsEndpointProbeMass m a x.2) : ℤ) : ℝ)| ≤ endpointError x.2
  spectral_gap_term_bound :
    ∀ x ∈ u.divisorsAntidiagonal, endpointError x.2 ≤ spectralGapTerm x.2

namespace xi_adams_fiber_mobius_inversion_finiten_error_data

/-- The finite-`N` Möbius estimator on the fixed odd fiber. -/
def estimated_exact_order_mass (D : xi_adams_fiber_mobius_inversion_finiten_error_data) : ℤ :=
  Finset.sum D.u.divisorsAntidiagonal
    (fun x => (μ x.1 : ℤ) * adamsEndpointProbeMass D.mhat D.a x.2)

/-- Deterministic endpoint-error budget obtained by summing the Möbius-weighted endpoint defects. -/
def deterministic_error_bound (D : xi_adams_fiber_mobius_inversion_finiten_error_data) : Prop :=
  |((D.estimated_exact_order_mass : ℤ) : ℝ) - D.f (2 ^ D.a * D.u)| ≤
    ∑ x ∈ D.u.divisorsAntidiagonal, D.endpointError x.2

/-- Spectral-gap budget obtained by dominating each endpoint defect termwise. -/
def spectral_gap_error_bound (D : xi_adams_fiber_mobius_inversion_finiten_error_data) : Prop :=
  |((D.estimated_exact_order_mass : ℤ) : ℝ) - D.f (2 ^ D.a * D.u)| ≤
    ∑ x ∈ D.u.divisorsAntidiagonal, D.spectralGapTerm x.2

lemma xi_adams_fiber_mobius_inversion_finiten_error_exact_recovery
    (D : xi_adams_fiber_mobius_inversion_finiten_error_data) :
    Finset.sum D.u.divisorsAntidiagonal
        (fun x => (μ x.1 : ℤ) * adamsEndpointProbeMass D.m D.a x.2) =
      adamsExactOrderMass D.f D.a D.u := by
  exact (paper_xi_adams_fiber_mobius_inversion D.m D.f D.a).mp D.endpointDecomposition
    D.u D.hu_pos D.hu_odd

lemma xi_adams_fiber_mobius_inversion_finiten_error_deterministic
    (D : xi_adams_fiber_mobius_inversion_finiten_error_data) :
    D.deterministic_error_bound := by
  have hExact := D.xi_adams_fiber_mobius_inversion_finiten_error_exact_recovery
  unfold deterministic_error_bound estimated_exact_order_mass
  calc
    |((Finset.sum D.u.divisorsAntidiagonal
          (fun x => (μ x.1 : ℤ) * adamsEndpointProbeMass D.mhat D.a x.2) : ℤ) : ℝ) -
        D.f (2 ^ D.a * D.u)| =
      |((Finset.sum D.u.divisorsAntidiagonal
            (fun x => (μ x.1 : ℤ) * adamsEndpointProbeMass D.mhat D.a x.2) -
          adamsExactOrderMass D.f D.a D.u : ℤ) : ℝ)| := by
        rw [show D.f (2 ^ D.a * D.u) = adamsExactOrderMass D.f D.a D.u by rfl]
        rw [← Int.cast_sub]
    _ =
        |((Finset.sum D.u.divisorsAntidiagonal
              (fun x => (μ x.1 : ℤ) * adamsEndpointProbeMass D.mhat D.a x.2) -
            Finset.sum D.u.divisorsAntidiagonal
              (fun x => (μ x.1 : ℤ) * adamsEndpointProbeMass D.m D.a x.2) : ℤ) : ℝ)| := by
          rw [hExact]
    _ =
        |((Finset.sum D.u.divisorsAntidiagonal
              (fun x =>
                (μ x.1 : ℤ) * adamsEndpointProbeMass D.mhat D.a x.2 -
                  (μ x.1 : ℤ) * adamsEndpointProbeMass D.m D.a x.2) : ℤ) : ℝ)| := by
          rw [Finset.sum_sub_distrib]
    _ = |∑ x ∈ D.u.divisorsAntidiagonal,
          ((((μ x.1 : ℤ) * adamsEndpointProbeMass D.mhat D.a x.2) -
              ((μ x.1 : ℤ) * adamsEndpointProbeMass D.m D.a x.2) : ℤ) : ℝ)| := by
          simp
    _ ≤ ∑ x ∈ D.u.divisorsAntidiagonal,
          |((((μ x.1 : ℤ) * adamsEndpointProbeMass D.mhat D.a x.2) -
              ((μ x.1 : ℤ) * adamsEndpointProbeMass D.m D.a x.2) : ℤ) : ℝ)| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x ∈ D.u.divisorsAntidiagonal, D.endpointError x.2 := by
          refine Finset.sum_le_sum ?_
          intro x hx
          exact D.term_error_bound x hx

lemma xi_adams_fiber_mobius_inversion_finiten_error_spectral
    (D : xi_adams_fiber_mobius_inversion_finiten_error_data) :
    D.spectral_gap_error_bound := by
  have hdet := D.xi_adams_fiber_mobius_inversion_finiten_error_deterministic
  unfold deterministic_error_bound at hdet
  unfold spectral_gap_error_bound
  exact hdet.trans <| Finset.sum_le_sum fun x hx => D.spectral_gap_term_bound x hx

end xi_adams_fiber_mobius_inversion_finiten_error_data

open xi_adams_fiber_mobius_inversion_finiten_error_data

/-- Paper label: `cor:xi-adams-fiber-mobius-inversion-finiteN-error`. The fixed odd-fiber
finite-`N` estimator differs from the exact Adams-fiber Möbius inversion by a Möbius-weighted sum
of endpoint errors, and any termwise spectral-gap control propagates to the full estimator. -/
theorem paper_xi_adams_fiber_mobius_inversion_finiten_error
    (D : xi_adams_fiber_mobius_inversion_finiten_error_data) :
    D.deterministic_error_bound ∧ D.spectral_gap_error_bound := by
  exact ⟨D.xi_adams_fiber_mobius_inversion_finiten_error_deterministic,
    D.xi_adams_fiber_mobius_inversion_finiten_error_spectral⟩

end Omega.Zeta
