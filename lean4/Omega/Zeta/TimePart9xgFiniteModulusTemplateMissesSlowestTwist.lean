import Mathlib.Tactic

namespace Omega.Zeta

theorem paper_xi_time_part9xg_finite_modulus_template_misses_slowest_twist
    (rhoRatio : Nat → ℝ) (M : Finset Nat) (rM : ℝ) (hrM_lt : rM < 1)
    (hcofinal :
      ∀ B : Nat,
        ∃ p : Nat, B ≤ p ∧ Nat.Prime p ∧ Odd p ∧ p ∉ M ∧ rM < rhoRatio p) :
    rM < 1 ∧
      ∀ B : Nat,
        ∃ p : Nat, B ≤ p ∧ Nat.Prime p ∧ Odd p ∧ p ∉ M ∧ rM < rhoRatio p := by
  exact ⟨hrM_lt, hcofinal⟩

end Omega.Zeta
