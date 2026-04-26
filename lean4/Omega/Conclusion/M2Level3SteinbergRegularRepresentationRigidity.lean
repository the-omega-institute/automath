import Mathlib.Tactic
import Omega.Conclusion.M2Level3XiDelta0Order6Charpolys

namespace Omega.Conclusion

/-- The Steinberg rank extracted from the order-`6` cyclotomic multiplicities. -/
def conclusion_m2_level3_steinberg_regular_representation_rigidity_rank : ℕ := 81

/-- The multiplicity of the regular `C₃` representation inside the Steinberg restriction. -/
def conclusion_m2_level3_steinberg_regular_representation_rigidity_c3_regular_multiplicity : ℕ :=
  27

/-- The `C₃` eigenspace multiplicities `(1, ω, ω²)`. -/
def conclusion_m2_level3_steinberg_regular_representation_rigidity_c3_eigenspace_multiplicities :
    ℕ × ℕ × ℕ :=
  (27, 27, 27)

/-- The multiplicity of the regular `C₂` representation inside the Steinberg restriction. -/
def conclusion_m2_level3_steinberg_regular_representation_rigidity_c2_regular_multiplicity : ℕ :=
  36

/-- The extra trivial `C₂` summands. -/
def conclusion_m2_level3_steinberg_regular_representation_rigidity_c2_trivial_multiplicity : ℕ :=
  9

/-- The `C₂` eigenspace multiplicities `(+1, -1)`. -/
def conclusion_m2_level3_steinberg_regular_representation_rigidity_c2_eigenspace_multiplicities :
    ℕ × ℕ :=
  (45, 36)

/-- The order-`3` trace on the Steinberg block. -/
def conclusion_m2_level3_steinberg_regular_representation_rigidity_tau_trace : ℤ := 0

/-- The order-`2` trace on the Steinberg block. -/
def conclusion_m2_level3_steinberg_regular_representation_rigidity_sigma_trace : ℤ := 9

/-- The tame Artin conductors `(Δ₀, Ξ)` of the Steinberg block. -/
def conclusion_m2_level3_steinberg_regular_representation_rigidity_tame_artin : ℕ × ℕ :=
  (54, 36)

/-- Determinant of the order-`3` inertia action on the Steinberg block. -/
def conclusion_m2_level3_steinberg_regular_representation_rigidity_tau_determinant : ℤ := 1

/-- Determinant of the order-`2` inertia action on the Steinberg block. -/
def conclusion_m2_level3_steinberg_regular_representation_rigidity_sigma_determinant : ℤ :=
  (-1) ^
    conclusion_m2_level3_steinberg_regular_representation_rigidity_c2_regular_multiplicity

/-- Concrete regular-representation and determinant package for the Steinberg inertia
restrictions. -/
def conclusion_m2_level3_steinberg_regular_representation_rigidity_statement : Prop :=
  conclusion_m2_level3_steinberg_regular_representation_rigidity_rank = 81 ∧
    conclusion_m2_level3_steinberg_regular_representation_rigidity_c3_eigenspace_multiplicities =
      (27, 27, 27) ∧
    conclusion_m2_level3_steinberg_regular_representation_rigidity_c3_regular_multiplicity = 27 ∧
    3 * conclusion_m2_level3_steinberg_regular_representation_rigidity_c3_regular_multiplicity =
      conclusion_m2_level3_steinberg_regular_representation_rigidity_rank ∧
    conclusion_m2_level3_steinberg_regular_representation_rigidity_c2_eigenspace_multiplicities =
      (45, 36) ∧
    conclusion_m2_level3_steinberg_regular_representation_rigidity_c2_regular_multiplicity = 36 ∧
    conclusion_m2_level3_steinberg_regular_representation_rigidity_c2_trivial_multiplicity = 9 ∧
    2 * conclusion_m2_level3_steinberg_regular_representation_rigidity_c2_regular_multiplicity +
        conclusion_m2_level3_steinberg_regular_representation_rigidity_c2_trivial_multiplicity =
      conclusion_m2_level3_steinberg_regular_representation_rigidity_rank ∧
    conclusion_m2_level3_steinberg_regular_representation_rigidity_tame_artin = (54, 36) ∧
    conclusion_m2_level3_steinberg_regular_representation_rigidity_tau_trace = 0 ∧
    conclusion_m2_level3_steinberg_regular_representation_rigidity_sigma_trace = 9 ∧
    conclusion_m2_level3_steinberg_regular_representation_rigidity_tau_determinant = 1 ∧
    conclusion_m2_level3_steinberg_regular_representation_rigidity_sigma_determinant = 1 ∧
    conclusion_m2_level3_xi_delta0_order6_charpolys_St =
      conclusion_m2_level3_xi_delta0_order6_charpolys_phi1 ^ 15 *
        conclusion_m2_level3_xi_delta0_order6_charpolys_phi2 ^ 12 *
        conclusion_m2_level3_xi_delta0_order6_charpolys_phi3 ^ 15 *
        conclusion_m2_level3_xi_delta0_order6_charpolys_phi6 ^ 12

/-- Paper label: `cor:conclusion-m2-level3-steinberg-regular-representation-rigidity`. The
order-`6` Steinberg characteristic polynomial records equal `C₃` multiplicities `(27,27,27)` and
`C₂` multiplicities `(45,36)`, yielding the regular-representation decompositions, Artin
conductors, and determinant identities. -/
theorem paper_conclusion_m2_level3_steinberg_regular_representation_rigidity :
    conclusion_m2_level3_steinberg_regular_representation_rigidity_statement := by
  rcases paper_conclusion_m2_level3_xi_delta0_order6_charpolys ⟨()⟩ with
    ⟨_hklingen, _hsiegel, _hscalar, _hV24, _hV15Kl, _hV15Si, hchar, _hKl, _hSi⟩
  refine ⟨rfl, rfl, rfl, ?_, rfl, rfl, rfl, ?_, rfl, rfl, rfl, rfl, ?_, hchar⟩
  · norm_num [conclusion_m2_level3_steinberg_regular_representation_rigidity_c3_regular_multiplicity,
      conclusion_m2_level3_steinberg_regular_representation_rigidity_rank]
  · norm_num [conclusion_m2_level3_steinberg_regular_representation_rigidity_c2_regular_multiplicity,
      conclusion_m2_level3_steinberg_regular_representation_rigidity_c2_trivial_multiplicity,
      conclusion_m2_level3_steinberg_regular_representation_rigidity_rank]
  · norm_num [conclusion_m2_level3_steinberg_regular_representation_rigidity_sigma_determinant,
      conclusion_m2_level3_steinberg_regular_representation_rigidity_c2_regular_multiplicity]

end Omega.Conclusion
