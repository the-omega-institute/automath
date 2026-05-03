import Mathlib.Tactic

namespace Omega.Zeta

universe u v

/-- Concrete correspondence data for the saturated shift-invariant lattice gcd/lcm rule.
The record keeps the lattice operations, the principal-generator correspondence, and the
transport of intersection and saturated sum through principal ideals in one prefixed package. -/
structure xi_saturated_shift_invariant_lattice_gcd_lcm_data where
  Lattice : Type u
  Polynomial : Type v
  P : Lattice → Polynomial
  M : Polynomial → Lattice
  meet : Lattice → Lattice → Lattice
  satJoin : Lattice → Lattice → Lattice
  gcd : Polynomial → Polynomial → Polynomial
  lcm : Polynomial → Polynomial → Polynomial
  idealIntersection : Polynomial → Polynomial → Polynomial
  idealSaturatedSum : Polynomial → Polynomial → Polynomial
  meet_correspondence :
    ∀ L1 L2 : Lattice, meet L1 L2 = M (idealIntersection (P L1) (P L2))
  satJoin_correspondence :
    ∀ L1 L2 : Lattice, satJoin L1 L2 = M (idealSaturatedSum (P L1) (P L2))
  idealIntersection_eq_lcm :
    ∀ P1 P2 : Polynomial, idealIntersection P1 P2 = lcm P1 P2
  idealSaturatedSum_eq_gcd :
    ∀ P1 P2 : Polynomial, idealSaturatedSum P1 P2 = gcd P1 P2

/-- Paper label: `cor:xi-saturated-shift-invariant-lattice-gcd-lcm`. -/
theorem paper_xi_saturated_shift_invariant_lattice_gcd_lcm
    (D : xi_saturated_shift_invariant_lattice_gcd_lcm_data) (L1 L2 : D.Lattice) :
    D.meet L1 L2 = D.M (D.lcm (D.P L1) (D.P L2)) ∧
      D.satJoin L1 L2 = D.M (D.gcd (D.P L1) (D.P L2)) := by
  constructor
  · rw [D.meet_correspondence, D.idealIntersection_eq_lcm]
  · rw [D.satJoin_correspondence, D.idealSaturatedSum_eq_gcd]

end Omega.Zeta
