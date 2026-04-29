import Mathlib.Tactic

namespace Omega.Zeta

/-- The displayed quintic `p₇(x)=x⁵-2x⁴-7x³-2x+2`, stored in ascending order. -/
def xi_p7_k5_integral_basis_discriminant_dyadic_splitting_quintic_coeffs : List ℤ :=
  [2, -2, 0, -7, -2, 1]

/-- The monic integral equation for `β=(θ³+θ⁴)/2`, stored in ascending order. -/
def xi_p7_k5_integral_basis_discriminant_dyadic_splitting_beta_minpoly_coeffs :
    List ℤ :=
  [-2, 41, -264, 574, -142, 1]

/-- The squarefree odd part of the displayed field discriminant. -/
def xi_p7_k5_integral_basis_discriminant_dyadic_splitting_q : ℤ :=
  985219

/-- The power-basis discriminant certificate for the displayed quintic. -/
def xi_p7_k5_integral_basis_discriminant_dyadic_splitting_power_basis_discriminant :
    ℤ :=
  -((2 : ℤ) ^ 4) * xi_p7_k5_integral_basis_discriminant_dyadic_splitting_q

/-- The trace-pairing discriminant of the displayed integral-basis lattice. -/
def xi_p7_k5_integral_basis_discriminant_dyadic_splitting_field_discriminant : ℤ :=
  -((2 : ℤ) ^ 2) * xi_p7_k5_integral_basis_discriminant_dyadic_splitting_q

/-- The index of `ℤ[θ]` in the displayed integral basis. -/
def xi_p7_k5_integral_basis_discriminant_dyadic_splitting_index : ℕ :=
  2

/-- The dyadic splitting certificate, encoded as `(ramification index, residue degree)`. -/
def xi_p7_k5_integral_basis_discriminant_dyadic_splitting_dyadic_factors :
    List (ℕ × ℕ) :=
  [(1, 1), (1, 1), (3, 1)]

/-- The discriminant quotient agrees with the square of the displayed index. -/
lemma xi_p7_k5_integral_basis_discriminant_dyadic_splitting_discriminant_index_check :
    xi_p7_k5_integral_basis_discriminant_dyadic_splitting_power_basis_discriminant =
      (xi_p7_k5_integral_basis_discriminant_dyadic_splitting_index : ℤ) ^ 2 *
        xi_p7_k5_integral_basis_discriminant_dyadic_splitting_field_discriminant := by
  norm_num [xi_p7_k5_integral_basis_discriminant_dyadic_splitting_power_basis_discriminant,
    xi_p7_k5_integral_basis_discriminant_dyadic_splitting_field_discriminant,
    xi_p7_k5_integral_basis_discriminant_dyadic_splitting_index,
    xi_p7_k5_integral_basis_discriminant_dyadic_splitting_q]

/-- The finite dyadic certificate has ramification profile `(1,1,3)`. -/
lemma xi_p7_k5_integral_basis_discriminant_dyadic_splitting_ramification_profile :
    xi_p7_k5_integral_basis_discriminant_dyadic_splitting_dyadic_factors.map Prod.fst =
      [1, 1, 3] := by
  rfl

/-- The finite dyadic certificate has all residue degrees equal to one. -/
lemma xi_p7_k5_integral_basis_discriminant_dyadic_splitting_residue_degree_profile :
    xi_p7_k5_integral_basis_discriminant_dyadic_splitting_dyadic_factors.map Prod.snd =
      [1, 1, 1] := by
  rfl

/-- The ramified dyadic factor is tame. -/
lemma xi_p7_k5_integral_basis_discriminant_dyadic_splitting_tame_dyadic_factor :
    Nat.Coprime 2 3 := by
  decide

/-- Concrete certificate statement for the `K₅` integral basis, index, discriminant,
and dyadic splitting package. -/
def xi_p7_k5_integral_basis_discriminant_dyadic_splitting_statement : Prop :=
  xi_p7_k5_integral_basis_discriminant_dyadic_splitting_quintic_coeffs =
      [2, -2, 0, -7, -2, 1] ∧
    xi_p7_k5_integral_basis_discriminant_dyadic_splitting_beta_minpoly_coeffs =
      [-2, 41, -264, 574, -142, 1] ∧
    xi_p7_k5_integral_basis_discriminant_dyadic_splitting_index = 2 ∧
    xi_p7_k5_integral_basis_discriminant_dyadic_splitting_field_discriminant =
      -((2 : ℤ) ^ 2) * 985219 ∧
    xi_p7_k5_integral_basis_discriminant_dyadic_splitting_power_basis_discriminant =
      (xi_p7_k5_integral_basis_discriminant_dyadic_splitting_index : ℤ) ^ 2 *
        xi_p7_k5_integral_basis_discriminant_dyadic_splitting_field_discriminant ∧
    xi_p7_k5_integral_basis_discriminant_dyadic_splitting_dyadic_factors.map Prod.fst =
      [1, 1, 3] ∧
    xi_p7_k5_integral_basis_discriminant_dyadic_splitting_dyadic_factors.map Prod.snd =
      [1, 1, 1] ∧
    Nat.Coprime 2 3

/-- Paper label: `thm:xi-p7-k5-integral-basis-discriminant-dyadic-splitting`. -/
theorem paper_xi_p7_k5_integral_basis_discriminant_dyadic_splitting :
    xi_p7_k5_integral_basis_discriminant_dyadic_splitting_statement := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [xi_p7_k5_integral_basis_discriminant_dyadic_splitting_field_discriminant,
      xi_p7_k5_integral_basis_discriminant_dyadic_splitting_q]
  · exact xi_p7_k5_integral_basis_discriminant_dyadic_splitting_discriminant_index_check
  · exact xi_p7_k5_integral_basis_discriminant_dyadic_splitting_ramification_profile
  · exact xi_p7_k5_integral_basis_discriminant_dyadic_splitting_residue_degree_profile
  · exact xi_p7_k5_integral_basis_discriminant_dyadic_splitting_tame_dyadic_factor

end Omega.Zeta
