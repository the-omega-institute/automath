import Mathlib.Tactic
import Omega.Zeta.XiP7S5GlobalArtinConductorsRho456

namespace Omega.Zeta

/-- Concrete arithmetic data for the P7/S5 conductor-discriminant compatibility theorem. -/
structure xi_p7_s5_discriminant_conductor_compatibility_and_relative_discriminant_data where
  xi_p7_s5_discriminant_conductor_compatibility_and_relative_discriminant_q : Nat
  xi_p7_s5_discriminant_conductor_compatibility_and_relative_discriminant_q_prime :
    Nat.Prime xi_p7_s5_discriminant_conductor_compatibility_and_relative_discriminant_q

/-- The `rho_4` conductor extracted from the already verified conductor triple. -/
def xi_p7_s5_discriminant_conductor_compatibility_and_relative_discriminant_rho4Conductor
    (q : Nat) : Nat :=
  (xi_p7_s5_global_artin_conductors_rho456_conductors q).1

/-- The `rho_5` conductor extracted from the already verified conductor triple. -/
def xi_p7_s5_discriminant_conductor_compatibility_and_relative_discriminant_rho5Conductor
    (q : Nat) : Nat :=
  (xi_p7_s5_global_artin_conductors_rho456_conductors q).2.1

/-- The `rho_6` conductor extracted from the already verified conductor triple. -/
def xi_p7_s5_discriminant_conductor_compatibility_and_relative_discriminant_rho6Conductor
    (q : Nat) : Nat :=
  (xi_p7_s5_global_artin_conductors_rho456_conductors q).2.2

/-- The discriminant of the quintic subfield in the conductor-product model. -/
def xi_p7_s5_discriminant_conductor_compatibility_and_relative_discriminant_discK5
    (D : xi_p7_s5_discriminant_conductor_compatibility_and_relative_discriminant_data) : Int :=
  -((xi_p7_s5_discriminant_conductor_compatibility_and_relative_discriminant_rho4Conductor
    D.xi_p7_s5_discriminant_conductor_compatibility_and_relative_discriminant_q : Nat) : Int)

/-- The discriminant of the degree-ten subfield in the conductor-product model. -/
def xi_p7_s5_discriminant_conductor_compatibility_and_relative_discriminant_discK10
    (D : xi_p7_s5_discriminant_conductor_compatibility_and_relative_discriminant_data) : Int :=
  -(((xi_p7_s5_discriminant_conductor_compatibility_and_relative_discriminant_rho4Conductor
      D.xi_p7_s5_discriminant_conductor_compatibility_and_relative_discriminant_q) *
    (xi_p7_s5_discriminant_conductor_compatibility_and_relative_discriminant_rho5Conductor
      D.xi_p7_s5_discriminant_conductor_compatibility_and_relative_discriminant_q) : Nat) : Int)

/-- The discriminant of the degree-twenty subfield in the conductor-product model. -/
def xi_p7_s5_discriminant_conductor_compatibility_and_relative_discriminant_discK20
    (D : xi_p7_s5_discriminant_conductor_compatibility_and_relative_discriminant_data) : Int :=
  -((((xi_p7_s5_discriminant_conductor_compatibility_and_relative_discriminant_rho4Conductor
      D.xi_p7_s5_discriminant_conductor_compatibility_and_relative_discriminant_q) ^ 2) *
    (xi_p7_s5_discriminant_conductor_compatibility_and_relative_discriminant_rho5Conductor
      D.xi_p7_s5_discriminant_conductor_compatibility_and_relative_discriminant_q) *
    (xi_p7_s5_discriminant_conductor_compatibility_and_relative_discriminant_rho6Conductor
      D.xi_p7_s5_discriminant_conductor_compatibility_and_relative_discriminant_q) : Nat) : Int)

/-- The norm of the relative discriminant in the quadratic tower. -/
def xi_p7_s5_discriminant_conductor_compatibility_and_relative_discriminant_relativeNorm
    (D : xi_p7_s5_discriminant_conductor_compatibility_and_relative_discriminant_data) : Nat :=
  D.xi_p7_s5_discriminant_conductor_compatibility_and_relative_discriminant_q

/-- Conductor values, the two explicit discriminants, and the single-prime relative norm. -/
def xi_p7_s5_discriminant_conductor_compatibility_and_relative_discriminant_statement
    (D : xi_p7_s5_discriminant_conductor_compatibility_and_relative_discriminant_data) : Prop :=
  let q := D.xi_p7_s5_discriminant_conductor_compatibility_and_relative_discriminant_q
  let f4 :=
    xi_p7_s5_discriminant_conductor_compatibility_and_relative_discriminant_rho4Conductor q
  let f5 :=
    xi_p7_s5_discriminant_conductor_compatibility_and_relative_discriminant_rho5Conductor q
  let f6 :=
    xi_p7_s5_discriminant_conductor_compatibility_and_relative_discriminant_rho6Conductor q
  f4 = 2 ^ 2 * q ∧
    f5 = 2 ^ 4 * q ^ 2 ∧
    f6 = 2 ^ 4 * q ^ 3 ∧
    xi_p7_s5_discriminant_conductor_compatibility_and_relative_discriminant_discK5 D =
      -((f4 : Nat) : Int) ∧
    xi_p7_s5_discriminant_conductor_compatibility_and_relative_discriminant_discK10 D =
      -(((f4 * f5 : Nat) : Int)) ∧
    xi_p7_s5_discriminant_conductor_compatibility_and_relative_discriminant_discK20 D =
      -((((f4 ^ 2) * f5 * f6 : Nat) : Int)) ∧
    xi_p7_s5_discriminant_conductor_compatibility_and_relative_discriminant_discK10 D =
      -(((2 ^ 6 * q ^ 3 : Nat) : Int)) ∧
    xi_p7_s5_discriminant_conductor_compatibility_and_relative_discriminant_discK20 D =
      -(((2 ^ 12 * q ^ 7 : Nat) : Int)) ∧
    Int.natAbs
        (xi_p7_s5_discriminant_conductor_compatibility_and_relative_discriminant_discK20 D) =
      Int.natAbs
          (xi_p7_s5_discriminant_conductor_compatibility_and_relative_discriminant_discK10 D) ^ 2 *
        xi_p7_s5_discriminant_conductor_compatibility_and_relative_discriminant_relativeNorm D ∧
    Nat.Prime
      (xi_p7_s5_discriminant_conductor_compatibility_and_relative_discriminant_relativeNorm D)

/-- Paper label:
`thm:xi-p7-s5-discriminant-conductor-compatibility-and-relative-discriminant`. -/
theorem paper_xi_p7_s5_discriminant_conductor_compatibility_and_relative_discriminant
    (D : xi_p7_s5_discriminant_conductor_compatibility_and_relative_discriminant_data) :
    xi_p7_s5_discriminant_conductor_compatibility_and_relative_discriminant_statement D := by
  rcases D with ⟨q, hq⟩
  simp [xi_p7_s5_discriminant_conductor_compatibility_and_relative_discriminant_statement,
    xi_p7_s5_discriminant_conductor_compatibility_and_relative_discriminant_rho4Conductor,
    xi_p7_s5_discriminant_conductor_compatibility_and_relative_discriminant_rho5Conductor,
    xi_p7_s5_discriminant_conductor_compatibility_and_relative_discriminant_rho6Conductor,
    xi_p7_s5_discriminant_conductor_compatibility_and_relative_discriminant_discK5,
    xi_p7_s5_discriminant_conductor_compatibility_and_relative_discriminant_discK10,
    xi_p7_s5_discriminant_conductor_compatibility_and_relative_discriminant_discK20,
    xi_p7_s5_discriminant_conductor_compatibility_and_relative_discriminant_relativeNorm,
    xi_p7_s5_global_artin_conductors_rho456_conductors,
    xi_p7_s5_global_artin_conductors_rho456_global_conductor,
    xi_p7_s5_global_artin_conductors_rho456_local_conductor_exponent, hq]
  refine ⟨?_, ?_, ?_⟩
  · ring_nf
  · ring_nf
  · simp [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
    ring

end Omega.Zeta
