import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-fold-uniform-baseline-testing-constant`. -/
theorem paper_xi_fold_uniform_baseline_testing_constant
    (Limit : (ℕ → ℝ) → ℝ → Prop) (tv bayes : ℕ → ℝ)
    (htv : Limit tv (1 - 2 / Real.sqrt 5))
    (hmap : ∀ f a, Limit f a → Limit (fun m => (1 - f m) / 2) ((1 - a) / 2))
    (hbayes : ∀ m, bayes m = (1 - tv m) / 2) :
    Limit tv (1 - 2 / Real.sqrt 5) ∧ Limit bayes (1 / Real.sqrt 5) := by
  refine ⟨htv, ?_⟩
  have hfun : bayes = fun m => (1 - tv m) / 2 := funext hbayes
  rw [hfun]
  have hconst : 1 / Real.sqrt 5 = (1 - (1 - 2 / Real.sqrt 5)) / 2 := by
    ring_nf
  rw [hconst]
  exact hmap tv (1 - 2 / Real.sqrt 5) htv

end Omega.Zeta
