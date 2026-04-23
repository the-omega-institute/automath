import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- The concrete elementary `2`-group `(ℤ/2ℤ)^ν`. -/
abbrev conclusion_elementary_2group_minimal_torus_dimension_elementary_2group (ν : ℕ) :=
  Fin ν → ZMod 2

/-- The `2`-torsion subgroup of the coordinate torus `𝕋^r`, modeled here by its sign coordinates. -/
abbrev conclusion_elementary_2group_minimal_torus_dimension_torus_two_torsion (r : ℕ) :=
  Fin r → ZMod 2

/-- A faithful phase model of the elementary `2`-group on `r` torus sign coordinates. -/
def conclusion_elementary_2group_minimal_torus_dimension_faithful_phase_model
    (ν r : ℕ) : Prop :=
  ∃ ρ :
      conclusion_elementary_2group_minimal_torus_dimension_elementary_2group ν →+
        conclusion_elementary_2group_minimal_torus_dimension_torus_two_torsion r,
    Function.Injective ρ

private lemma conclusion_elementary_2group_minimal_torus_dimension_lower_bound
    {ν r : ℕ}
    (hρ :
      conclusion_elementary_2group_minimal_torus_dimension_faithful_phase_model ν r) :
    ν ≤ r := by
  rcases hρ with ⟨ρ, hρinj⟩
  have hcard :
      Fintype.card
          (conclusion_elementary_2group_minimal_torus_dimension_elementary_2group ν) ≤
        Fintype.card
          (conclusion_elementary_2group_minimal_torus_dimension_torus_two_torsion r) :=
    Fintype.card_le_of_injective ρ hρinj
  have hpows : 2 ^ ν ≤ 2 ^ r := by
    simpa [
      conclusion_elementary_2group_minimal_torus_dimension_elementary_2group,
      conclusion_elementary_2group_minimal_torus_dimension_torus_two_torsion
    ] using hcard
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hpows

/-- The coordinate sign embedding realizing the sharp `r = ν` case. -/
def conclusion_elementary_2group_minimal_torus_dimension_coordinate_sign_embedding
    (ν : ℕ) :
    conclusion_elementary_2group_minimal_torus_dimension_elementary_2group ν →+
      conclusion_elementary_2group_minimal_torus_dimension_torus_two_torsion ν :=
  AddMonoidHom.id _

/-- Paper label: `thm:conclusion-elementary-2group-minimal-torus-dimension`. Any faithful torus
sign-coordinate realization of `(ℤ/2ℤ)^ν` needs at least `ν` coordinates, and equality is realized
by the coordinate sign embedding. -/
theorem paper_conclusion_elementary_2group_minimal_torus_dimension (ν : ℕ) :
    (∀ r,
        conclusion_elementary_2group_minimal_torus_dimension_faithful_phase_model ν r →
          ν ≤ r) ∧
      conclusion_elementary_2group_minimal_torus_dimension_faithful_phase_model ν ν := by
  refine ⟨?_, ?_⟩
  · intro r hρ
    exact conclusion_elementary_2group_minimal_torus_dimension_lower_bound hρ
  · refine ⟨
      conclusion_elementary_2group_minimal_torus_dimension_coordinate_sign_embedding ν,
      ?_⟩
    intro x y hxy
    simpa using hxy

end Omega.Conclusion
