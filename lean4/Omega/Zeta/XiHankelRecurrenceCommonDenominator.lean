import Omega.Zeta.HankelMaximalMinorSyndromeNormalFormUniqueness

namespace Omega.Zeta

/-- Denominator-clearing bridge: divisibility of the absolute determinant gives divisibility of
the signed integer determinant. -/
lemma xi_hankel_recurrence_common_denominator_divides_determinants_int_dvd_of_natAbs
    {D : Nat} {z : Int} (h : D ∣ z.natAbs) : (D : Int) ∣ z := by
  exact Int.natCast_dvd.mpr h

/-- Abstract Cramer-style clearing interface for Hankel recurrence denominators: if every
nonzero maximal minor clears the common denominator, then that denominator divides each nonzero
signed determinant.
    cor:xi-hankel-recurrence-common-denominator-divides-determinants -/
theorem paper_xi_hankel_recurrence_common_denominator_divides_determinants (D : Nat)
    (clears : Nat → Prop) (detH : Nat → Int) (hmin : ∀ N, clears N → D ∣ N)
    (hdet : ∀ ell, detH ell ≠ 0 → clears (Int.natAbs (detH ell))) :
    ∀ ell, detH ell ≠ 0 → (D : Int) ∣ detH ell := by
  intro ell hne
  exact xi_hankel_recurrence_common_denominator_divides_determinants_int_dvd_of_natAbs
    (hmin (Int.natAbs (detH ell)) (hdet ell hne))

end Omega.Zeta
