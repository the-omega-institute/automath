import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `cor:pom-toggle-dihedral-orientation-character`. -/
theorem paper_pom_toggle_dihedral_orientation_character (ell : Nat)
    (orientationCharacterTrivial scanEven timeReversalEven : Prop)
    (htrivial : orientationCharacterTrivial ↔ scanEven ∧ timeReversalEven)
    (hscan : scanEven ↔ ell % 6 = 0 ∨ ell % 6 = 2 ∨ ell % 6 = 4 ∨ ell % 6 = 5)
    (htime : timeReversalEven ↔
      ell % 12 = 0 ∨ ell % 12 = 1 ∨ ell % 12 = 5 ∨
        ell % 12 = 9 ∨ ell % 12 = 10 ∨ ell % 12 = 11) :
    orientationCharacterTrivial ↔
      ell % 12 = 0 ∨ ell % 12 = 5 ∨ ell % 12 = 10 ∨ ell % 12 = 11 := by
  rw [htrivial, hscan, htime]
  constructor
  · rintro ⟨hs, ht⟩
    rcases hs with hs | hs | hs | hs <;>
      rcases ht with ht | ht | ht | ht | ht | ht <;>
        omega
  · intro h
    rcases h with h | h | h | h
    · constructor
      · left
        omega
      · left
        exact h
    · constructor
      · right; right; right
        omega
      · right; right; left
        exact h
    · constructor
      · right; right; left
        omega
      · right; right; right; right; left
        exact h
    · constructor
      · right; right; right
        omega
      · right; right; right; right; right
        exact h

end Omega.POM
