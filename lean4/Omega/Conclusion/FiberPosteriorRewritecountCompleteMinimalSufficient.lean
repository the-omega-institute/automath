import Mathlib

namespace Omega.Conclusion

open scoped BigOperators

/-- Normalizing polynomial of the one-parameter posterior family. -/
def conclusion_fiber_posterior_rewritecount_complete_minimal_sufficient_partitionFunction
    (N : Nat → Nat) (q : Nat) (t : ℝ) : ℝ :=
  Finset.sum (Finset.range (q + 1)) fun k => (N k : ℝ) * t ^ k

/-- Unnormalized exponential-family factor carried by the rewrite-count statistic. -/
def conclusion_fiber_posterior_rewritecount_complete_minimal_sufficient_factor
    (t : ℝ) (k : Nat) : ℝ :=
  t ^ k

/-- Posterior weight on a fiber element. -/
noncomputable def conclusion_fiber_posterior_rewritecount_complete_minimal_sufficient_posterior
    {Ω : Type*} (r : Ω → Nat) (N : Nat → Nat) (q : Nat) (t : ℝ) (ω : Ω) : ℝ :=
  conclusion_fiber_posterior_rewritecount_complete_minimal_sufficient_factor t (r ω) /
    conclusion_fiber_posterior_rewritecount_complete_minimal_sufficient_partitionFunction N q t

/-- Polynomial whose coefficients encode the centered expectations `h(k) N(k)`. -/
noncomputable def conclusion_fiber_posterior_rewritecount_complete_minimal_sufficient_statisticPolynomial
    (h : Nat → ℝ) (N : Nat → Nat) (q : Nat) : Polynomial ℝ :=
  Finset.sum (Finset.range (q + 1))
    fun k => Polynomial.monomial k (h k * (N k : ℝ))

/-- Paper label: `thm:conclusion-fiber-posterior-rewritecount-complete-minimal-sufficient`.
The posterior is an exponential family in the statistic `r`, equality of all positive-activity
fibers is detected already at `t = 2`, and a polynomial identity forces every coefficient to
vanish on the gap-free support `0, …, q`. -/
theorem paper_conclusion_fiber_posterior_rewritecount_complete_minimal_sufficient :
    ∀ {Ω : Type*} [Fintype Ω] (r : Ω → Nat) (N : Nat → Nat) (q : Nat)
      (hN : ∀ k ≤ q, 0 < N k),
      (∀ t ω,
          conclusion_fiber_posterior_rewritecount_complete_minimal_sufficient_posterior
              r N q t ω =
            (conclusion_fiber_posterior_rewritecount_complete_minimal_sufficient_partitionFunction
                N q t)⁻¹ *
              conclusion_fiber_posterior_rewritecount_complete_minimal_sufficient_factor t
                (r ω)) ∧
        (∀ ω ω',
            (∀ t : ℝ, 0 < t →
                conclusion_fiber_posterior_rewritecount_complete_minimal_sufficient_factor t
                    (r ω) =
                  conclusion_fiber_posterior_rewritecount_complete_minimal_sufficient_factor t
                    (r ω')) ↔
              r ω = r ω') ∧
        (∀ h : Nat → ℝ,
            (∀ t : ℝ,
                (conclusion_fiber_posterior_rewritecount_complete_minimal_sufficient_statisticPolynomial
                    h N q).eval t = 0) →
              ∀ k ≤ q, h k = 0) := by
  intro Ω _ r N q hN
  refine ⟨?_, ?_, ?_⟩
  · intro t ω
    simp [conclusion_fiber_posterior_rewritecount_complete_minimal_sufficient_posterior,
      conclusion_fiber_posterior_rewritecount_complete_minimal_sufficient_factor, div_eq_mul_inv,
      mul_comm, mul_left_comm, mul_assoc]
  · intro ω ω'
    constructor
    · intro hEq
      have htwo :
          conclusion_fiber_posterior_rewritecount_complete_minimal_sufficient_factor (2 : ℝ)
              (r ω) =
            conclusion_fiber_posterior_rewritecount_complete_minimal_sufficient_factor (2 : ℝ)
              (r ω') :=
        hEq 2 (by norm_num)
      exact (pow_right_injective₀ (show (0 : ℝ) < 2 by norm_num) (by norm_num : (2 : ℝ) ≠ 1))
        htwo
    · intro hstat
      intro t ht
      simp [conclusion_fiber_posterior_rewritecount_complete_minimal_sufficient_factor, hstat]
  · intro h hpoly k hk
    have hzero :
        conclusion_fiber_posterior_rewritecount_complete_minimal_sufficient_statisticPolynomial h N q
          = 0 := by
      apply Polynomial.funext
      intro t
      simpa using hpoly t
    have hcoeff :
        h k * (N k : ℝ) = 0 := by
      have hcoeff_zero :
          Finset.sum (Finset.range (q + 1))
            (fun b => (Polynomial.monomial b (h b * (N b : ℝ))).coeff k) = 0 := by
        simpa [conclusion_fiber_posterior_rewritecount_complete_minimal_sufficient_statisticPolynomial]
          using congrArg (fun p : Polynomial ℝ => p.coeff k) hzero
      have hk_mem : k ∈ Finset.range (q + 1) := by
        exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hk)
      rw [Finset.sum_eq_single k] at hcoeff_zero
      · simpa using hcoeff_zero
      · intro b hb hbk
        simp [Polynomial.coeff_monomial, hbk]
      · intro hk_not_mem
        exact False.elim (hk_not_mem hk_mem)
    have hNk : (N k : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (hN k hk))
    exact (mul_eq_zero.mp hcoeff).resolve_right hNk

end Omega.Conclusion
