import Mathlib.Tactic
import Omega.SPG.ExactScreenMinimaAreMatroidBases

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-window6-exact-screen-minimal-size-64`. -/
theorem paper_conclusion_window6_exact_screen_minimal_size_64
    {V : Type*} [DecidableEq V]
    (r : Finset V → ℕ)
    (hzero : r ∅ = 0)
    (hrho : ∀ s, r s ≤ 64)
    (hrcard : ∀ s, r s ≤ s.card)
    (hmono : ∀ {s t : Finset V}, s ⊆ t → r s ≤ r t)
    (hsub : ∀ s t, r (s ∩ t) + r (s ∪ t) ≤ r s + r t)
    (hstep : ∀ s, r s < 64 → ∃ v ∉ s, r (insert v s) = r s + 1) :
    ∃ B : Finset V, r B = 64 ∧ B.card = 64 ∧
      ∀ T : Finset V, r T = 64 → 64 ≤ T.card := by
  exact
    Omega.SPG.paper_spg_exact_screen_minima_are_matroid_bases 64 r hzero hrho hrcard
      hmono hsub hstep

end Omega.Conclusion
