import Mathlib.Tactic

namespace Omega.Conclusion

/-- Tail-factor witness for the exact one-step Markov law and Riccati recursion in the
Zeckendorf-Godel density package. The prefix-product formula is treated as prior input; this
structure records the tail factors and the two scalar recursions obtained by expanding `Mₙ₊₁`
against `e₀` and `e₁`. -/
structure ZGInhomogeneousMarkovWitness where
  p : ℕ → ℚ
  A : ℕ → ℚ
  B : ℕ → ℚ
  condProb : ℕ → Bool → ℚ
  p_pos : ∀ n, 0 < p n
  A_pos : ∀ n, 0 < A n
  B_nonneg : ∀ n, 0 ≤ B n
  cond_one : ∀ n, condProb n true = 0
  cond_zero :
    ∀ n, condProb n false = B (n + 1) / (p (n + 1) * A (n + 1) + B (n + 1))
  A_rec :
    ∀ n,
      A n =
        (p (n + 1) / (p (n + 1) + 1)) * A (n + 1) +
          (1 / (p (n + 1) + 1)) * B (n + 1)
  B_rec : ∀ n, B n = (p (n + 1) / (p (n + 1) + 1)) * A (n + 1)

set_option maxHeartbeats 400000 in
/-- Paper-facing exact inhomogeneous Markov package for the ZG density measure: the one-step
conditional law only depends on the last symbol, and the tail ratio `rₙ = Bₙ / Aₙ` satisfies the
Riccati recursion obtained by scalarizing the matrix tail recurrence.
    thm:conclusion-zg-density-exact-inhomogeneous-markov -/
theorem paper_conclusion_zg_density_exact_inhomogeneous_markov
    (w : ZGInhomogeneousMarkovWitness) :
    (∀ n,
      w.condProb n true = 0 ∧
        w.condProb n false =
          w.B (n + 1) / (w.p (n + 1) * w.A (n + 1) + w.B (n + 1))) ∧
      (∀ n,
        w.B n / w.A n =
          w.p (n + 1) / (w.p (n + 1) + w.B (n + 1) / w.A (n + 1))) ∧
      (∀ n,
        w.condProb n false =
          (w.B (n + 1) / w.A (n + 1)) /
            (w.p (n + 1) + w.B (n + 1) / w.A (n + 1))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    exact ⟨w.cond_one n, w.cond_zero n⟩
  · intro n
    have hp : 0 < w.p (n + 1) := w.p_pos (n + 1)
    have hA : 0 < w.A (n + 1) := w.A_pos (n + 1)
    have hB : 0 ≤ w.B (n + 1) := w.B_nonneg (n + 1)
    have hp1 : w.p (n + 1) + 1 ≠ 0 := by linarith
    have hA0 : w.A (n + 1) ≠ 0 := by linarith
    have hden : w.p (n + 1) + w.B (n + 1) / w.A (n + 1) ≠ 0 := by
      have hnonneg : 0 ≤ w.B (n + 1) / w.A (n + 1) := by
        positivity
      linarith
    rw [w.B_rec n, w.A_rec n]
    field_simp [hp1, hA0, hden]
  · intro n
    have hA : 0 < w.A (n + 1) := w.A_pos (n + 1)
    have hp : 0 < w.p (n + 1) := w.p_pos (n + 1)
    have hB : 0 ≤ w.B (n + 1) := w.B_nonneg (n + 1)
    have hA0 : w.A (n + 1) ≠ 0 := by linarith
    have hden : w.p (n + 1) * w.A (n + 1) + w.B (n + 1) ≠ 0 := by
      have hpos : 0 < w.p (n + 1) * w.A (n + 1) + w.B (n + 1) := by positivity
      exact ne_of_gt hpos
    have hden' : w.p (n + 1) + w.B (n + 1) / w.A (n + 1) ≠ 0 := by
      have hnonneg : 0 ≤ w.B (n + 1) / w.A (n + 1) := by positivity
      linarith
    rw [w.cond_zero n]
    field_simp [hA0, hden, hden']

end Omega.Conclusion
