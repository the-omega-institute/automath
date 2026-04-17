import Mathlib.Tactic

namespace Omega.Zeta

/-- Data package for the normalized Zeckendorf--Godel prefix recursion. The fields record the
normalized prefix recursion, positivity of the decrement term, the normalization of the density
approximants, and the explicit tail estimate. -/
structure ZGPrefixRecursionData where
  p : ℕ → ℝ
  a : ℕ → ℝ
  b : ℕ → ℝ
  u : ℕ → ℝ
  deltaTilde : ℕ → ℝ
  deltaZG : ℝ
  zetaTwo : ℝ
  tailSeries : ℕ → ℝ
  prefixStep : ∀ N : ℕ, u (N + 1) = u N - b N / (p (N + 1) + 1)
  deltaNormalization : ∀ N : ℕ, deltaTilde N = u N / zetaTwo
  zetaTwoPos : 0 < zetaTwo
  decrementPos : ∀ N : ℕ, 0 < b N / (p (N + 1) + 1)
  lowerLimit : ∀ N : ℕ, deltaZG ≤ deltaTilde N
  explicitTailEstimate : ∀ N : ℕ, deltaTilde N - deltaZG ≤ deltaTilde N * tailSeries N

/-- The normalized prefix recursion for `u_N`. -/
def ZGPrefixRecursionData.prefixFormula (d : ZGPrefixRecursionData) : Prop :=
  ∀ N : ℕ, d.u (N + 1) = d.u N - d.b N / (d.p (N + 1) + 1)

/-- Strict monotonicity of the normalized approximants together with their lower limit bound. -/
def ZGPrefixRecursionData.monotoneConvergence (d : ZGPrefixRecursionData) : Prop :=
  (∀ N : ℕ, d.deltaTilde (N + 1) < d.deltaTilde N) ∧ ∀ N : ℕ, d.deltaZG ≤ d.deltaTilde N

/-- The explicit lower and upper tail certificate for the normalized approximation error. -/
def ZGPrefixRecursionData.explicitTailBound (d : ZGPrefixRecursionData) : Prop :=
  ∀ N : ℕ,
    0 ≤ d.deltaTilde N - d.deltaZG ∧ d.deltaTilde N - d.deltaZG ≤ d.deltaTilde N * d.tailSeries N

/-- The normalized prefix recursion forces strict monotonicity after dividing by `ζ(2)`, and the
certified explicit tail estimate gives the two-sided tail error bound.
    prop:xi-zg-prefix-recursion-monotone-tail-certificate -/
theorem paper_xi_zg_prefix_recursion_monotone_tail_certificate (d : ZGPrefixRecursionData) :
    d.prefixFormula ∧ d.monotoneConvergence ∧ d.explicitTailBound := by
  have hPrefix : d.prefixFormula := d.prefixStep
  have hMono : d.monotoneConvergence := by
    refine ⟨?_, d.lowerLimit⟩
    intro N
    have hu : d.u (N + 1) < d.u N := by
      rw [d.prefixStep N]
      have hDec : 0 < d.b N / (d.p (N + 1) + 1) := d.decrementPos N
      linarith
    rw [d.deltaNormalization (N + 1), d.deltaNormalization N]
    exact div_lt_div_of_pos_right hu d.zetaTwoPos
  have hTail : d.explicitTailBound := by
    intro N
    refine ⟨?_, d.explicitTailEstimate N⟩
    have hLower : d.deltaZG ≤ d.deltaTilde N := d.lowerLimit N
    linarith
  exact ⟨hPrefix, hMono, hTail⟩

end Omega.Zeta
