import Mathlib.Tactic

/-!
# Perfect zero-knowledge indistinguishability on a fiber

If all acceptance probabilities are constant on a fiber, a separator cannot realize probability
one on a nonempty query part and probability zero on a nonempty complement.
-/

namespace Omega.Zeta

/-- Paper label: `thm:xi-hankel-window-2dminus1-perfect-zk-indistinguishability`. -/
theorem paper_xi_hankel_window_2dminus1_perfect_zk_indistinguishability {A : Type*}
    (fiber query : A → Prop) (acceptProb : A → ℝ) (c : ℝ)
    (hconst : ∀ a, fiber a → acceptProb a = c) :
    ¬ (∃ sep : A → ℝ, (∀ a, fiber a → sep a = acceptProb a) ∧
      (∀ a, fiber a → query a → sep a = 1) ∧
      (∀ a, fiber a → ¬ query a → sep a = 0) ∧
      (∃ a, fiber a ∧ query a) ∧ (∃ a, fiber a ∧ ¬ query a)) := by
  rintro ⟨sep, hsep, hquery, hnotQuery, ⟨a, hafiber, haquery⟩, ⟨b, hbfiber, hbnotQuery⟩⟩
  have hc_one : c = 1 := by
    calc
      c = acceptProb a := (hconst a hafiber).symm
      _ = sep a := (hsep a hafiber).symm
      _ = 1 := hquery a hafiber haquery
  have hc_zero : c = 0 := by
    calc
      c = acceptProb b := (hconst b hbfiber).symm
      _ = sep b := (hsep b hbfiber).symm
      _ = 0 := hnotQuery b hbfiber hbnotQuery
  linarith

end Omega.Zeta
