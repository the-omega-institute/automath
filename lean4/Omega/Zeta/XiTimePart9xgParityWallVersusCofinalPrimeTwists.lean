import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9xg-parity-wall-versus-cofinal-prime-twists`. -/
theorem paper_xi_time_part9xg_parity_wall_versus_cofinal_prime_twists
    (rhoRatio : Nat → ℝ) (rhoMinusOverLambda : ℝ) (hwall : rhoMinusOverLambda < 1)
    (hcofinal :
      ∀ B : Nat,
        ∃ p : Nat, B ≤ p ∧ Nat.Prime p ∧ Odd p ∧ rhoMinusOverLambda < rhoRatio p) :
    rhoMinusOverLambda < 1 ∧
      ∀ B : Nat,
        ∃ p : Nat, B ≤ p ∧ Nat.Prime p ∧ Odd p ∧ rhoMinusOverLambda < rhoRatio p := by
  exact ⟨hwall, hcofinal⟩

end Omega.Zeta
