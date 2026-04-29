import Omega.Zeta.XiComovingPrefixEndpointBarrierLaw

namespace Omega.Zeta

/-- The recursive dyadic-center choice inherits the endpoint-margin lower bound from the
one-shot comoving-prefix barrier law when the prefix depth is `m`. -/
def xi_comoving_prefix_recursive_bisection_margin_bound (T delta0 : ℝ) (m : ℕ) : Prop :=
  0 < delta0 → delta0 ≤ 1 / 2 →
    ∀ {δ Δ : ℝ}, delta0 ≤ δ → δ ≤ 1 / 2 →
      Δ ^ (2 : ℕ) ≤ (xiComovingPrefixError T m) ^ (2 : ℕ) →
      xiComovingEndpointMargin (xiComovingPrefixError T m) delta0 ≤ xiComovingEndpointMargin Δ δ

/-- The recursive bisection budget is the endpoint-barrier budget specialized to prefix depth `m`,
so the dyadic error scale is `T * 2^{-m}`. -/
def xi_comoving_prefix_recursive_bisection_budget_drop (T delta0 : ℝ) (m : ℕ) : Prop :=
  0 < delta0 → delta0 ≤ 1 / 2 →
    xiComovingPrefixPmin T delta0 m =
      Real.log (((T * (2 : ℝ) ^ (-(m : ℝ))) ^ (2 : ℕ) + (1 + delta0) ^ (2 : ℕ)) /
          (4 * delta0)) /
        Real.log 2

/-- Paper label: `thm:xi-comoving-prefix-recursive-bisection`. The depth-`m` dyadic center is just
the `B = m` instance of the audited comoving-prefix endpoint barrier law. -/
theorem paper_xi_comoving_prefix_recursive_bisection (T delta0 : ℝ) (m : ℕ) :
    xi_comoving_prefix_recursive_bisection_margin_bound T delta0 m ∧
      xi_comoving_prefix_recursive_bisection_budget_drop T delta0 m := by
  refine ⟨?_, ?_⟩
  · intro hdelta0 hdelta0_half δ Δ hδ hδ_half hΔ
    have hbarrier :=
      paper_xi_comoving_prefix_endpoint_barrier_law (T := T) (δ₀ := delta0) (B := m)
        hdelta0 hdelta0_half
    exact hbarrier.1 hδ hδ_half hΔ
  · intro hdelta0 hdelta0_half
    have hbarrier :=
      paper_xi_comoving_prefix_endpoint_barrier_law (T := T) (δ₀ := delta0) (B := m)
        hdelta0 hdelta0_half
    simpa [xiComovingPrefixError] using hbarrier.2

end Omega.Zeta
