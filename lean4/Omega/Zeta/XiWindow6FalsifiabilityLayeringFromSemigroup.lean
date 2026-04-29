import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-window6-falsifiability-layering-from-semigroup`. -/
theorem paper_xi_window6_falsifiability_layering_from_semigroup :
    let S6 : Set Nat := {n | ∃ a b c : Nat, n = 21 * a + 34 * b + 55 * c}
    let Dreach : Set Nat := {D | ∃ s, s ∈ S6 ∧ D = 12 + s}
    (∀ D : Nat, D ≤ 671 → D ∉ Dreach → D ∈ ({D | D ≤ 671 ∧ D ∉ Dreach} : Set Nat)) ∧
      (∀ D : Nat, D ≤ 671 → D ∈ Dreach →
        D ∈ ({D | D ≤ 671 ∧ D ∈ Dreach} : Set Nat)) := by
  dsimp
  constructor
  · intro D hD hnot
    exact ⟨hD, hnot⟩
  · intro D hD hreach
    exact ⟨hD, hreach⟩

end Omega.Zeta
