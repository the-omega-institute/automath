import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-exceptional-theta-omega-identification`. Two integer sequences with
the same first two values and the same second-order recurrence agree at every index. -/
theorem paper_xi_exceptional_theta_omega_identification (m : ℕ) (L s : ℤ)
    (Theta Omega : ℕ → ℤ) (hT0 : Theta 0 = 1) (hO0 : Omega 0 = 1)
    (hT1 : Theta 1 = L) (hO1 : Omega 1 = L)
    (hTrec : ∀ q, Theta (q + 2) = L * Theta (q + 1) - s * Theta q)
    (hOrec : ∀ q, Omega (q + 2) = L * Omega (q + 1) - s * Omega q) :
    ∀ q, Theta q = Omega q := by
  let _paperDepth := m
  have hpair : ∀ q, Theta q = Omega q ∧ Theta (q + 1) = Omega (q + 1) := by
    intro q
    induction q with
    | zero =>
        exact ⟨by rw [hT0, hO0], by rw [hT1, hO1]⟩
    | succ q ih =>
        refine ⟨ih.2, ?_⟩
        rw [hTrec q, hOrec q, ih.1, ih.2]
  intro q
  exact (hpair q).1

end Omega.Zeta
