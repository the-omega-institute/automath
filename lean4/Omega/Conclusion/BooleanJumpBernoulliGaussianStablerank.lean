import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

noncomputable section

open scoped BigOperators

/-- The concrete singular values in the Boolean-jump Bernoulli-Gaussian package. -/
def conclusion_boolean_jump_bernoulli_gaussian_stablerank_singular_value
    (q : ℕ) (_i : Fin q) : ℝ :=
  1

/-- The moment generating function of the associated Rademacher sum. -/
def conclusion_boolean_jump_bernoulli_gaussian_stablerank_mgf (q : ℕ) (t : ℝ) : ℝ :=
  ∏ _i : Fin q, Real.cosh t

/-- Stable rank computed from the singular values. -/
def conclusion_boolean_jump_bernoulli_gaussian_stablerank_stable_rank (q : ℕ) : ℝ :=
  ((∑ i : Fin q,
        (conclusion_boolean_jump_bernoulli_gaussian_stablerank_singular_value q i) ^ (2 : ℕ)) ^ 2) /
    ∑ i : Fin q,
      (conclusion_boolean_jump_bernoulli_gaussian_stablerank_singular_value q i) ^ (4 : ℕ)

/-- Concrete Bernoulli-Gaussian package: the mgf is the product law for `q` Rademachers and the
stable rank closes to `q`. -/
def conclusion_boolean_jump_bernoulli_gaussian_stablerank_statement (q : ℕ) : Prop :=
  (∀ t : ℝ,
    conclusion_boolean_jump_bernoulli_gaussian_stablerank_mgf q t = (Real.cosh t) ^ q) ∧
    conclusion_boolean_jump_bernoulli_gaussian_stablerank_stable_rank q = q

/-- The product mgf is immediate, and the stable-rank formula reduces to the constant singular
value computation. -/
theorem conclusion_boolean_jump_bernoulli_gaussian_stablerank_verified
    (q : ℕ) (hq : 1 ≤ q) :
    conclusion_boolean_jump_bernoulli_gaussian_stablerank_statement q := by
  refine ⟨?_, ?_⟩
  · intro t
    simp [conclusion_boolean_jump_bernoulli_gaussian_stablerank_mgf]
  · have hq_pos : 0 < q := Nat.lt_of_lt_of_le (Nat.succ_pos 0) hq
    have hq_ne : (q : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hq_pos)
    rw [conclusion_boolean_jump_bernoulli_gaussian_stablerank_stable_rank]
    simp [conclusion_boolean_jump_bernoulli_gaussian_stablerank_singular_value]
    field_simp [hq_ne]

/-- Paper label: `thm:conclusion-boolean-jump-bernoulli-gaussian-stablerank`. -/
def paper_conclusion_boolean_jump_bernoulli_gaussian_stablerank
    (q : ℕ) (_hq : 1 ≤ q) : Prop :=
  conclusion_boolean_jump_bernoulli_gaussian_stablerank_statement q

end

end Omega.Conclusion
