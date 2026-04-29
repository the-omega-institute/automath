import Mathlib.Tactic
import Omega.DerivedConsequences.DerivedLeyangCubicModelsCommonQuadraticResolvent
import Omega.Zeta.XiLeyangSplitPrimesQuadraticCharacterFilter

namespace Omega.DerivedConsequences

open Omega.Zeta

/-- Concrete parity-synchronization package: the common quadratic resolvent is `Q(√-111)`, and
every prime lies in the split or nonsplit parity branch according to the quadratic Frobenius sign.
-/
def derived_leyang_cubic_models_parity_synchronization_packaged_statement : Prop :=
  xiLeyangQuadraticSubfieldDiscriminant = -111 ∧
    ∀ p : ℕ,
      (xiLeyangQuadraticCharacter p = 1 ∧ xiLeyangSplitsCompletely p) ∨
        (xiLeyangQuadraticCharacter p = -1 ∧ ¬ xiLeyangSplitsCompletely p)

local notation "derived_leyang_cubic_models_parity_synchronization_statement" =>
  derived_leyang_cubic_models_parity_synchronization_packaged_statement

/-- Paper label: `cor:derived-leyang-cubic-models-parity-synchronization`. -/
theorem paper_derived_leyang_cubic_models_parity_synchronization :
    derived_leyang_cubic_models_parity_synchronization_statement := by
  refine ⟨?_, ?_⟩
  · exact paper_derived_leyang_cubic_models_common_quadratic_resolvent.2.2.2
  · intro p
    by_cases hχ : xiLeyangQuadraticCharacter p = 1
    · exact Or.inl ⟨hχ, hχ⟩
    · by_cases hp : p ∈ xiLeyangQuadraticRamifiedPrimes
      · refine Or.inr ⟨?_, ?_⟩
        · simp [xiLeyangQuadraticCharacter, hp]
        · simp [xiLeyangSplitsCompletely, xiLeyangQuadraticCharacter, hp]
      · have hχ' : xiLeyangQuadraticCharacter p = 1 := by
          simp [xiLeyangQuadraticCharacter, hp]
        exact (hχ hχ').elim

end Omega.DerivedConsequences
