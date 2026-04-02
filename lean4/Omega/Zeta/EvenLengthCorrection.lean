import Mathlib.Tactic

namespace Omega.Zeta

def evenLengthCorrection (v n : Nat) : Nat :=
  if Even n then 2 * v ^ (n / 2) else 0

/-- Odd lengths contribute no even-length atomic correction.
    thm:xi-time-part73c-periodic-evenlength-atomic-correction -/
theorem evenLengthCorrection_odd (v n : Nat) (hn : ¬ Even n) :
    evenLengthCorrection v n = 0 := by
  simp [evenLengthCorrection, hn]

/-- Even lengths contribute the half-length monomial term.
    thm:xi-time-part73c-periodic-evenlength-atomic-correction -/
theorem evenLengthCorrection_even (v m : Nat) :
    evenLengthCorrection v (2 * m) = 2 * v ^ m := by
  simp [evenLengthCorrection]

/-- Case split form of the even-length correction.
    thm:xi-time-part73c-periodic-evenlength-atomic-correction -/
theorem evenLengthCorrection_cases (v n : Nat) :
    evenLengthCorrection v n =
      if Even n then 2 * v ^ (n / 2) else 0 := by
  rfl

end Omega.Zeta
