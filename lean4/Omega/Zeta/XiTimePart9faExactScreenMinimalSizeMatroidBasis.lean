import Mathlib.Tactic
import Omega.SPG.ExactScreenMinimaAreMatroidBases

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9fa-exact-screen-minimal-size-matroid-basis`. -/
theorem paper_xi_time_part9fa_exact_screen_minimal_size_matroid_basis {V : Type*}
    [DecidableEq V] (m n : ℕ) (r : Finset V → ℕ) (hzero : r ∅ = 0)
    (hrho : ∀ S, r S ≤ 2 ^ (m * n)) (hrcard : ∀ S, r S ≤ S.card)
    (hmono : ∀ {S T}, S ⊆ T → r S ≤ r T)
    (hsub : ∀ S T, r (S ∩ T) + r (S ∪ T) ≤ r S + r T)
    (hstep : ∀ S, r S < 2 ^ (m * n) → ∃ v ∉ S, r (insert v S) = r S + 1) :
    ∃ B : Finset V,
      r B = 2 ^ (m * n) ∧
        B.card = 2 ^ (m * n) ∧
          ∀ T : Finset V, r T = 2 ^ (m * n) → 2 ^ (m * n) ≤ T.card := by
  exact
    Omega.SPG.paper_spg_exact_screen_minima_are_matroid_bases (2 ^ (m * n)) r
      hzero hrho hrcard hmono hsub hstep

end Omega.Zeta
