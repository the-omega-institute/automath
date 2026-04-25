import Mathlib.Tactic

namespace Omega.Conclusion

/-- The tail law predicted by Haar invariance: coherence at depth at least `n` has mass
`B^(-2n)`. -/
def conclusion_godel_leyang_haar_coherence_depth_tail_probability (B n : ℕ) : ℚ :=
  1 / (B ^ (2 * n) : ℚ)

/-- The exact depth law recovered by differencing adjacent tails. -/
def conclusion_godel_leyang_haar_coherence_depth_point_probability (B n : ℕ) : ℚ :=
  conclusion_godel_leyang_haar_coherence_depth_tail_probability B n -
    conclusion_godel_leyang_haar_coherence_depth_tail_probability B (n + 1)

/-- Paper label: `prop:conclusion-godel-leyang-haar-coherence-depth`. The point law is the
difference of the Haar tails, hence carries the geometric factor `(1 - B⁻²)`. -/
theorem paper_conclusion_godel_leyang_haar_coherence_depth {B n : ℕ} (hB : 0 < B) :
    conclusion_godel_leyang_haar_coherence_depth_tail_probability B n =
      1 / (B ^ (2 * n) : ℚ) ∧
      conclusion_godel_leyang_haar_coherence_depth_point_probability B n =
        (1 - 1 / (B ^ 2 : ℚ)) * (1 / (B ^ (2 * n) : ℚ)) := by
  refine ⟨rfl, ?_⟩
  unfold conclusion_godel_leyang_haar_coherence_depth_point_probability
    conclusion_godel_leyang_haar_coherence_depth_tail_probability
  have hBq : (B : ℚ) ≠ 0 := by exact_mod_cast hB.ne'
  have hpow : (B ^ (2 * (n + 1)) : ℚ) = (B ^ (2 * n) : ℚ) * (B ^ 2 : ℚ) := by
    rw [show 2 * (n + 1) = 2 * n + 2 by omega, pow_add]
  rw [hpow]
  field_simp [hBq]

end Omega.Conclusion
