import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

set_option maxHeartbeats 400000 in
/-- The two decision regions `δ = 1` and `δ = 0` partition the finite hidden-bit sample space, so
their total probability mass is `1`.
    cor:conclusion-maxfiber-hiddenbit-balanced-bayes-wall -/
theorem paper_conclusion_maxfiber_hiddenbit_balanced_bayes_wall
    (n : ℕ) (w : (Fin n → Bool) → ℝ) (δ : (Fin n → Bool) → Fin 2)
    (hprob : (∑ ω, w ω) = 1) :
    (Finset.univ.filter (fun ω => δ ω = 1)).sum w +
      (Finset.univ.filter (fun ω => δ ω = 0)).sum w = 1 := by
  have hfilter :
      (Finset.univ.filter fun ω : (Fin n → Bool) => δ ω = 0) =
        Finset.univ.filter (fun ω : (Fin n → Bool) => δ ω ≠ 1) := by
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hzero
      simp [hzero]
    · intro hne
      have hcases : δ ω = 0 ∨ δ ω = 1 := by
        have hk : (δ ω).1 = 0 ∨ (δ ω).1 = 1 := by
          have hlt : (δ ω).1 < 2 := (δ ω).2
          omega
        cases hk with
        | inl hk =>
            exact Or.inl (Fin.ext hk)
        | inr hk =>
            exact Or.inr (Fin.ext hk)
      rcases hcases with hzero | hone
      · exact hzero
      · exfalso
        exact hne hone
  calc
    (Finset.univ.filter (fun ω => δ ω = 1)).sum w +
        (Finset.univ.filter (fun ω => δ ω = 0)).sum w =
      (Finset.univ.filter (fun ω => δ ω = 1)).sum w +
        (Finset.univ.filter (fun ω => δ ω ≠ 1)).sum w := by
          rw [hfilter]
    _ = ∑ ω, w ω := by
          simpa using
            (Finset.sum_filter_add_sum_filter_not
              (s := Finset.univ) (p := fun ω : (Fin n → Bool) => δ ω = 1) (f := w))
    _ = 1 := hprob

end Omega.Conclusion
