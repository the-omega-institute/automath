import Omega.Conclusion.PrimitiveLengthTwoAdditiveFourierRankOne

namespace Omega.Conclusion

noncomputable section

open scoped BigOperators

/-- Concrete finite character-projection data for the primitive length-two atom. -/
structure conclusion_primitive_atom_character_rigidity_data where
  q : ℕ
  hq : 2 ≤ q
  chi : Fin q → ℂ
  z : ℂ
  u : ℂ

/-- The residue-class primitive atom profile `A_q(a; z, u)`, supported only at `a = 2`. -/
def conclusion_primitive_atom_character_rigidity_atom
    (D : conclusion_primitive_atom_character_rigidity_data) (a : Fin D.q) : ℂ :=
  conclusion_primitive_length_two_additive_fourier_rank_one_profile D.q D.hq a * D.u * D.z ^ 2

/-- The finite character projection of the primitive atom profile. -/
def conclusion_primitive_atom_character_rigidity_projection
    (D : conclusion_primitive_atom_character_rigidity_data) : ℂ :=
  ∑ a : Fin D.q, D.chi a * conclusion_primitive_atom_character_rigidity_atom D a

/-- The value of the character at the distinguished residue class `2 mod q`. -/
def conclusion_primitive_atom_character_rigidity_chi_two
    (D : conclusion_primitive_atom_character_rigidity_data) : ℂ :=
  D.chi (conclusion_primitive_length_two_additive_fourier_rank_one_residue D.q D.hq)

/-- Concrete statement: the character projection only sees the residue class `2 mod q`. -/
def conclusion_primitive_atom_character_rigidity_statement
    (D : conclusion_primitive_atom_character_rigidity_data) : Prop :=
  conclusion_primitive_atom_character_rigidity_projection D =
    conclusion_primitive_atom_character_rigidity_chi_two D * D.u * D.z ^ 2

/-- Paper label: `cor:conclusion-primitive-atom-character-rigidity`. -/
theorem paper_conclusion_primitive_atom_character_rigidity
    (D : conclusion_primitive_atom_character_rigidity_data) :
    conclusion_primitive_atom_character_rigidity_statement D := by
  classical
  have _hrank := conclusion_primitive_length_two_additive_fourier_rank_one_verified D.q D.hq
  simp [conclusion_primitive_atom_character_rigidity_statement,
    conclusion_primitive_atom_character_rigidity_projection,
    conclusion_primitive_atom_character_rigidity_atom,
    conclusion_primitive_atom_character_rigidity_chi_two,
    conclusion_primitive_length_two_additive_fourier_rank_one_profile]
  ring

end

end Omega.Conclusion
