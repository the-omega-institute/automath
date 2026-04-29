import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-local-zero-count-closure-budget`. -/
theorem paper_xi_local_zero_count_closure_budget {k : ℕ} (f : ℝ → ℝ) (T1 T2 : ℝ)
    (tau radius gamma drift : Fin k → ℝ)
    (hLocal : ∀ j : Fin k,
      T1 < gamma j ∧ gamma j < T2 ∧ |gamma j - tau j| < radius j ∧
        f (gamma j) = 0 ∧ |gamma j - tau j| ≤ drift j)
    (hUnique : ∀ j : Fin k, ∀ t : ℝ, |t - tau j| < radius j → f t = 0 →
      t = gamma j)
    (hCover : ∀ t : ℝ, T1 ≤ t → t ≤ T2 → f t = 0 →
      ∃ j : Fin k, |t - tau j| < radius j)
    (hInjective : Function.Injective gamma) :
    ((∀ t : ℝ, T1 ≤ t → t ≤ T2 → f t = 0 → ∃! j : Fin k, t = gamma j) ∧
      ∀ j : Fin k, |gamma j - tau j| ≤ drift j) := by
  constructor
  · intro t hT1 hT2 ht
    rcases hCover t hT1 hT2 ht with ⟨j, hj⟩
    have htj : t = gamma j := hUnique j t hj ht
    refine ⟨j, htj, ?_⟩
    intro i hti
    exact hInjective (by
      calc
        gamma i = t := hti.symm
        _ = gamma j := htj)
  · intro j
    exact (hLocal j).2.2.2.2

end Omega.Zeta
