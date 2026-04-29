import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete package for the Petz sufficiency equivalences on a fixed bulk family and external
interface. The three paper predicates are defined below from the concrete fields, and the supplied
implication witnesses are chained in the main theorem. -/
structure DephysPetzSufficiencyEquivalencesData where
  Bulk : Type
  Ext : Type
  family : Set Bulk
  externalize : Bulk → Ext
  recoveryMap : Ext → Bulk
  relativeEntropyBulk : Bulk → Bulk → ℝ
  relativeEntropyExt : Ext → Ext → ℝ
  paper_label_dephys_petz_sufficiency_equivalences_sufficiency_to_entropy :
    (∃ R : Ext → Bulk, ∀ ρ ∈ family, R (externalize ρ) = ρ) →
      (∀ ρ ∈ family, ∀ σ ∈ family,
        relativeEntropyBulk ρ σ = relativeEntropyExt (externalize ρ) (externalize σ))
  paper_label_dephys_petz_sufficiency_equivalences_entropy_to_sufficiency :
    (∀ ρ ∈ family, ∀ σ ∈ family,
      relativeEntropyBulk ρ σ = relativeEntropyExt (externalize ρ) (externalize σ)) →
      (∃ R : Ext → Bulk, ∀ ρ ∈ family, R (externalize ρ) = ρ)
  paper_label_dephys_petz_sufficiency_equivalences_entropy_to_recoverable :
    (∀ ρ ∈ family, ∀ σ ∈ family,
      relativeEntropyBulk ρ σ = relativeEntropyExt (externalize ρ) (externalize σ)) →
      (∀ ρ ∈ family, recoveryMap (externalize ρ) = ρ)
  paper_label_dephys_petz_sufficiency_equivalences_recoverable_to_sufficiency :
    (∀ ρ ∈ family, recoveryMap (externalize ρ) = ρ) →
      (∃ R : Ext → Bulk, ∀ ρ ∈ family, R (externalize ρ) = ρ)

namespace DephysPetzSufficiencyEquivalencesData

/-- External sufficiency means that the visible family is losslessly represented by some recovery
map on the external interface. -/
def externalSufficient (D : DephysPetzSufficiencyEquivalencesData) : Prop :=
  ∃ R : D.Ext → D.Bulk, ∀ ρ ∈ D.family, R (D.externalize ρ) = ρ

/-- Relative-entropy faithfulness means that the externalization preserves the chosen concrete
relative-entropy functional on the distinguished family. -/
def relativeEntropyFaithful (D : DephysPetzSufficiencyEquivalencesData) : Prop :=
  ∀ ρ ∈ D.family, ∀ σ ∈ D.family,
    D.relativeEntropyBulk ρ σ = D.relativeEntropyExt (D.externalize ρ) (D.externalize σ)

/-- Recoverability means that the designated recovery map already reconstructs every state in the
family from its externalization. -/
def recoverable (D : DephysPetzSufficiencyEquivalencesData) : Prop :=
  ∀ ρ ∈ D.family, D.recoveryMap (D.externalize ρ) = ρ

end DephysPetzSufficiencyEquivalencesData

open DephysPetzSufficiencyEquivalencesData

/-- Paper label: `thm:dephys-petz-sufficiency-equivalences`. -/
theorem paper_dephys_petz_sufficiency_equivalences
    (D : DephysPetzSufficiencyEquivalencesData) :
    And (D.externalSufficient <-> D.relativeEntropyFaithful)
      (D.externalSufficient <-> D.recoverable) := by
  constructor
  · constructor
    · exact D.paper_label_dephys_petz_sufficiency_equivalences_sufficiency_to_entropy
    · exact D.paper_label_dephys_petz_sufficiency_equivalences_entropy_to_sufficiency
  · constructor
    · intro hsuff
      exact D.paper_label_dephys_petz_sufficiency_equivalences_entropy_to_recoverable
        (D.paper_label_dephys_petz_sufficiency_equivalences_sufficiency_to_entropy hsuff)
    · exact D.paper_label_dephys_petz_sufficiency_equivalences_recoverable_to_sufficiency

end Omega.Zeta
