import Mathlib.Tactic

namespace Omega.Zeta

/-- The window-`6` orbit histogram has `8` orbits of size `2`. -/
def window6AbstractOrbitMultiplicityTwo : Nat := 8

/-- The window-`6` orbit histogram has `4` orbits of size `3`. -/
def window6AbstractOrbitMultiplicityThree : Nat := 4

/-- The window-`6` orbit histogram has `9` orbits of size `4`. -/
def window6AbstractOrbitMultiplicityFour : Nat := 9

/-- Orbit size of the homogeneous `C₁₂`-set `C₁₂ / C_d`. -/
def c12OrbitSizeFromStabilizer (d : Nat) : Nat := 12 / d

/-- The sharp `C₁₂` witness uses the disjoint union `8 * (C₁₂ / C₆) + 4 * (C₁₂ / C₄) +
9 * (C₁₂ / C₃)`. -/
def window6AbstractC12WitnessHistogram : List (Nat × Nat) :=
  [(c12OrbitSizeFromStabilizer 6, window6AbstractOrbitMultiplicityTwo),
    (c12OrbitSizeFromStabilizer 4, window6AbstractOrbitMultiplicityThree),
    (c12OrbitSizeFromStabilizer 3, window6AbstractOrbitMultiplicityFour)]

/-- Total cardinality of the explicit `C₁₂` witness. -/
def window6AbstractC12WitnessPointCount : Nat :=
  window6AbstractOrbitMultiplicityTwo * c12OrbitSizeFromStabilizer 6 +
    window6AbstractOrbitMultiplicityThree * c12OrbitSizeFromStabilizer 4 +
    window6AbstractOrbitMultiplicityFour * c12OrbitSizeFromStabilizer 3

/-- Concrete paper statement: every acting group order realizing orbit sizes `2, 3, 4` is
divisible by `12`, and the explicit `C₁₂` witness has the required histogram and total size `64`.
-/
def Window6AbstractOrbittypeMinimalC12Statement : Prop :=
  (∀ n : Nat, 2 ∣ n → 3 ∣ n → 4 ∣ n → 12 ∣ n) ∧
    Nat.lcm (Nat.lcm 2 3) 4 = 12 ∧
    window6AbstractC12WitnessHistogram = [(2, 8), (3, 4), (4, 9)] ∧
    window6AbstractC12WitnessPointCount = 64

/-- Paper label: `thm:xi-time-part70da-window6-abstract-orbittype-minimal-c12`.
Orbit sizes `2`, `3`, and `4` force divisibility by `lcm(2,3,4) = 12`, and the disjoint union
`8 * (C₁₂ / C₆) + 4 * (C₁₂ / C₄) + 9 * (C₁₂ / C₃)` realizes the sharp witness with `64` points. -/
theorem paper_xi_time_part70da_window6_abstract_orbittype_minimal_c12 :
    Window6AbstractOrbittypeMinimalC12Statement := by
  refine ⟨?_, by decide, by native_decide, by native_decide⟩
  intro n h2 h3 h4
  have h6 : Nat.lcm 2 3 ∣ n := Nat.lcm_dvd h2 h3
  have h12 : Nat.lcm (Nat.lcm 2 3) 4 ∣ n := Nat.lcm_dvd h6 h4
  simpa using h12

end Omega.Zeta
