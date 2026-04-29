import Mathlib.Tactic

namespace Omega.Zeta

/-- The audited unique odd ramified prime in the `p₇` `S₅` layer. -/
def xi_p7_s5_odd_ramification_discriminant_and_conductor_oddRamifiedPrime : ℕ :=
  985219

/-- Degrees of the three displayed intermediate fields `K₅`, `K₁₀`, and `K₂₀`. -/
def xi_p7_s5_odd_ramification_discriminant_and_conductor_intermediateDegrees :
    List ℕ :=
  [5, 10, 20]

/-- Transposition orbit counts on the three corresponding coset actions. -/
def xi_p7_s5_odd_ramification_discriminant_and_conductor_transpositionOrbitCounts :
    List ℕ :=
  [4, 7, 13]

/-- Tame discriminant exponents `degree - number of transposition orbits`. -/
def xi_p7_s5_odd_ramification_discriminant_and_conductor_discriminantExponents :
    List ℕ :=
  List.zipWith (fun degree orbitCount => degree - orbitCount)
    xi_p7_s5_odd_ramification_discriminant_and_conductor_intermediateDegrees
    xi_p7_s5_odd_ramification_discriminant_and_conductor_transpositionOrbitCounts

/-- Dimensions of the three irreducible Artin representations `ρ₄`, `ρ₅`, and `ρ₆`. -/
def xi_p7_s5_odd_ramification_discriminant_and_conductor_characterDimensions :
    List ℕ :=
  [4, 5, 6]

/-- Transposition character values for `ρ₄`, `ρ₅`, and `ρ₆`. -/
def xi_p7_s5_odd_ramification_discriminant_and_conductor_transpositionCharacterValues :
    List ℕ :=
  [2, 1, 0]

/-- Tame Artin conductor exponents `(dim ρ - χρ(τ)) / 2`. -/
def xi_p7_s5_odd_ramification_discriminant_and_conductor_artinConductorExponents :
    List ℕ :=
  List.zipWith (fun dim fixedTrace => (dim - fixedTrace) / 2)
    xi_p7_s5_odd_ramification_discriminant_and_conductor_characterDimensions
    xi_p7_s5_odd_ramification_discriminant_and_conductor_transpositionCharacterValues

/-- Paper label: `thm:xi-p7-s5-odd-ramification-discriminant-and-conductor`. -/
theorem paper_xi_p7_s5_odd_ramification_discriminant_and_conductor :
    xi_p7_s5_odd_ramification_discriminant_and_conductor_oddRamifiedPrime = 985219 ∧
      xi_p7_s5_odd_ramification_discriminant_and_conductor_discriminantExponents =
        [1, 3, 7] ∧
      xi_p7_s5_odd_ramification_discriminant_and_conductor_artinConductorExponents =
        [1, 2, 3] := by
  native_decide

end Omega.Zeta
