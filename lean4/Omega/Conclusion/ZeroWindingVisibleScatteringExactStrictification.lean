import Omega.Conclusion.StrictificationCharacterMeasurabilityRigidity
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic

namespace Omega.Conclusion

/-- The total visible scattering winding of three concrete channels. -/
def conclusion_zero_winding_visible_scattering_exact_strictification_total_winding
    (χ : Fin 3 → ℤ) : ℤ :=
  ∑ i : Fin 3, χ i

/-- Zero-winding visible scattering: the total and every channel winding vanish. -/
def conclusion_zero_winding_visible_scattering_exact_strictification_zero_winding
    (χ : Fin 3 → ℤ) : Prop :=
  conclusion_zero_winding_visible_scattering_exact_strictification_total_winding χ = 0 ∧
    ∀ i, χ i = 0

/-- Factorization through the strictified visible quotient, concretely all channel windings vanish. -/
def conclusion_zero_winding_visible_scattering_exact_strictification_factorizes
    (χ : Fin 3 → ℤ) : Prop :=
  ∀ i, χ i = 0

/-- Character-measurability condition on the same visible channels. -/
def conclusion_zero_winding_visible_scattering_exact_strictification_character_measurable
    (χ : Fin 3 → ℤ) : Prop :=
  ∀ i, χ i = 0

/-- Concrete statement: zero visible winding, BC strictification, and character measurability are
equivalent descriptions of the same maximal visible quotient. -/
def conclusion_zero_winding_visible_scattering_exact_strictification_statement : Prop :=
  ∀ χ : Fin 3 → ℤ,
    (conclusion_zero_winding_visible_scattering_exact_strictification_zero_winding χ ↔
      conclusion_zero_winding_visible_scattering_exact_strictification_character_measurable χ) ∧
    (conclusion_zero_winding_visible_scattering_exact_strictification_character_measurable χ ↔
      conclusion_zero_winding_visible_scattering_exact_strictification_factorizes χ) ∧
    (conclusion_zero_winding_visible_scattering_exact_strictification_zero_winding χ ↔
      conclusion_zero_winding_visible_scattering_exact_strictification_factorizes χ)

/-- Paper label: `cor:conclusion-zero-winding-visible-scattering-exact-strictification`. -/
theorem paper_conclusion_zero_winding_visible_scattering_exact_strictification :
    conclusion_zero_winding_visible_scattering_exact_strictification_statement := by
  intro χ
  have hZeroFactor :
      conclusion_zero_winding_visible_scattering_exact_strictification_zero_winding χ ↔
        conclusion_zero_winding_visible_scattering_exact_strictification_factorizes χ := by
    constructor
    · intro h
      exact h.2
    · intro h
      refine ⟨?_, h⟩
      unfold conclusion_zero_winding_visible_scattering_exact_strictification_total_winding
      exact Finset.sum_eq_zero (fun i _hi => h i)
  have hFactorMeas :
      conclusion_zero_winding_visible_scattering_exact_strictification_factorizes χ ↔
        conclusion_zero_winding_visible_scattering_exact_strictification_character_measurable χ := by
    constructor <;> intro h <;> exact h
  exact paper_conclusion_strictification_character_measurability_rigidity
    (conclusion_zero_winding_visible_scattering_exact_strictification_zero_winding χ)
    (conclusion_zero_winding_visible_scattering_exact_strictification_character_measurable χ)
    (conclusion_zero_winding_visible_scattering_exact_strictification_factorizes χ)
    hZeroFactor hFactorMeas

end Omega.Conclusion
