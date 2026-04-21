import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic
import Omega.Conclusion.PrimeRegisterEllipseCompleteEquivalence

namespace Omega.Zeta

open Omega.Conclusion

/-- An integer axis-aligned ellipse is encoded by its two positive integral axes. -/
structure IntegerEllipse where
  majorAxis : ℕ+
  minorAxis : ℕ+

/-- Prime-register coordinates of the two axes. -/
def integerEllipsePrimeRegisterPair (E : IntegerEllipse) : PrimeRegisterVector × PrimeRegisterVector :=
  (Nat.factorizationEquiv E.majorAxis, Nat.factorizationEquiv E.minorAxis)

/-- Total prime multiplicity `Ω(n) = Σ_p v_p(n)` on positive integers. -/
def bigOmegaPNat (n : ℕ+) : ℕ :=
  ((n : ℕ).factorization).sum fun _ e => e

/-- The atomic word length of the integer ellipse monoid. -/
def integerEllipseAtomicLength (E : IntegerEllipse) : ℕ :=
  bigOmegaPNat E.majorAxis + bigOmegaPNat E.minorAxis

/-- Right divisibility in the axis-aligned ellipse monoid is coordinatewise divisibility. -/
def integerEllipseRightDivides (E F : IntegerEllipse) : Prop :=
  (E.majorAxis : ℕ) ∣ (F.majorAxis : ℕ) ∧ (E.minorAxis : ℕ) ∣ (F.minorAxis : ℕ)

/-- Prime-exponent formulation of coordinatewise divisibility. -/
def integerEllipseFactorizationLE (E F : IntegerEllipse) : Prop :=
  ((E.majorAxis : ℕ).factorization ≤ (F.majorAxis : ℕ).factorization) ∧
    ((E.minorAxis : ℕ).factorization ≤ (F.minorAxis : ℕ).factorization)

/-- Paper label: `thm:xi-time-part76-integer-ellipse-atomic-length-divisibility`.

Unique factorization identifies an integer ellipse with the pair of prime-exponent vectors of its
two axes, the atomic length is the sum `Ω(a) + Ω(b)`, and right divisibility is exactly the
coordinatewise divisibility order. -/
theorem paper_xi_time_part76_integer_ellipse_atomic_length_divisibility
    (E F : IntegerEllipse) :
    (integerEllipsePrimeRegisterPair E = integerEllipsePrimeRegisterPair F ↔ E = F) ∧
      integerEllipseAtomicLength E =
        ((E.majorAxis : ℕ).factorization).sum (fun _ e => e) +
          ((E.minorAxis : ℕ).factorization).sum (fun _ e => e) ∧
      (integerEllipseRightDivides E F ↔ integerEllipseFactorizationLE E F) := by
  refine ⟨?_, rfl, ?_⟩
  · constructor
    · intro h
      cases E with
      | mk a b =>
        cases F with
        | mk c d =>
          have hac : a = c := Nat.factorizationEquiv.injective (congrArg Prod.fst h)
          have hbd : b = d := Nat.factorizationEquiv.injective (congrArg Prod.snd h)
          cases hac
          cases hbd
          rfl
    · intro h
      cases h
      rfl
  · constructor
    · rintro ⟨hMajor, hMinor⟩
      refine ⟨?_, ?_⟩
      · exact (Nat.factorization_le_iff_dvd (Nat.ne_of_gt E.majorAxis.2) (Nat.ne_of_gt F.majorAxis.2)).2
          hMajor
      · exact (Nat.factorization_le_iff_dvd (Nat.ne_of_gt E.minorAxis.2) (Nat.ne_of_gt F.minorAxis.2)).2
          hMinor
    · rintro ⟨hMajor, hMinor⟩
      refine ⟨?_, ?_⟩
      · exact (Nat.factorization_le_iff_dvd (Nat.ne_of_gt E.majorAxis.2) (Nat.ne_of_gt F.majorAxis.2)).1
          hMajor
      · exact (Nat.factorization_le_iff_dvd (Nat.ne_of_gt E.minorAxis.2) (Nat.ne_of_gt F.minorAxis.2)).1
          hMinor

end Omega.Zeta
