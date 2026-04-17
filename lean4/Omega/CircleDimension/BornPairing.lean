import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.CircleDimension

open scoped BigOperators

/-- Concrete Born-pairing data: an event space with probabilities, an orthogonality relation, and
normalization on the complete family `Finset.univ`. -/
structure BornPairingData where
  Event : Type
  instFintype : Fintype Event
  instDecidableEq : DecidableEq Event
  prob : Event → ℝ
  orthogonal : Event → Event → Prop
  prob_nonneg : ∀ e, 0 ≤ prob e
  prob_le_one : ∀ e, prob e ≤ 1
  total_mass_univ : (∑ e : Event, prob e) = 1

attribute [instance] BornPairingData.instFintype BornPairingData.instDecidableEq

/-- A finite family is pairwise orthogonal when all distinct events in it are orthogonal. -/
def BornPairingData.pairwiseOrthogonal (D : BornPairingData) (F : Finset D.Event) : Prop :=
  ∀ ⦃e₁ e₂ : D.Event⦄, e₁ ∈ F → e₂ ∈ F → e₁ ≠ e₂ → D.orthogonal e₁ e₂

/-- Completeness is represented by containing all events. -/
def BornPairingData.complete (D : BornPairingData) (F : Finset D.Event) : Prop :=
  F = Finset.univ

/-- Paper label: `thm:cdim-born-pairing`. -/
theorem paper_cdim_born_pairing (D : BornPairingData) :
    (∀ e : D.Event, 0 ≤ D.prob e ∧ D.prob e ≤ 1) ∧
      (∀ F : Finset D.Event, D.pairwiseOrthogonal F → D.complete F → (∑ e ∈ F, D.prob e) = 1) := by
  refine ⟨?_, ?_⟩
  · intro e
    exact ⟨D.prob_nonneg e, D.prob_le_one e⟩
  · intro F _ hcomplete
    rw [BornPairingData.complete] at hcomplete
    subst F
    simpa using D.total_mass_univ

end Omega.CircleDimension
