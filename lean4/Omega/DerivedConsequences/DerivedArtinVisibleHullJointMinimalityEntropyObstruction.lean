import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.Conclusion.ArtinDeterminantMinimalVisibleQuotient
import Omega.EA.ChebotarevSecondMainTermWitness

namespace Omega.DerivedConsequences

open Omega.Conclusion
open Omega.EA
open conclusion_artin_determinant_minimal_visible_quotient_data

/-- Concrete joint visible-hull package: a determinant-active quotient, one dominant hidden
character detected by an active channel, and one further quotient kernel whose determinant
invariance is being tested. -/
structure derived_artin_visible_hull_joint_minimality_entropy_obstruction_data where
  joint : conclusion_artin_determinant_minimal_visible_quotient_data
  dominantChannel : joint.X
  dominantHidden : joint.G
  dominantCoeff : ℝ
  dominantCoeff_ne_zero : dominantCoeff ≠ 0
  dominantChannel_active : dominantChannel ∈ joint.active
  dominantChannel_detects_hidden : joint.channel dominantChannel dominantHidden ≠ 1
  furtherKernel : Subgroup joint.G
  furtherKernel_preserves_determinant :
    PrimitiveCarrierInvariant furtherKernel joint.determinantProfile

/-- The square shadow of the dominant hidden-channel witness. -/
def derived_artin_visible_hull_joint_minimality_entropy_obstruction_entropy_shadow
    (h : derived_artin_visible_hull_joint_minimality_entropy_obstruction_data) (n : ℕ) : ℝ :=
  |kernelWitnessTerm h.dominantCoeff n| ^ 2

/-- The joint visible quotient is uniquely minimal, any determinant-preserving further quotient
must remain inside the determinant kernel, the chosen dominant hidden character therefore cannot
be deleted, and its square shadow survives with the exact dominant amplitude on both parity
subsequences. -/
def derived_artin_visible_hull_joint_minimality_entropy_obstruction_statement
    (h : derived_artin_visible_hull_joint_minimality_entropy_obstruction_data) : Prop :=
  h.joint.unique_minimality ∧
    h.furtherKernel ≤ h.joint.N_det ∧
    h.dominantHidden ∉ h.furtherKernel ∧
    0 < |spectralProjection h.dominantCoeff| ^ 2 ∧
    ∀ n : ℕ,
      derived_artin_visible_hull_joint_minimality_entropy_obstruction_entropy_shadow h (2 * n) =
          |spectralProjection h.dominantCoeff| ^ 2 ∧
        derived_artin_visible_hull_joint_minimality_entropy_obstruction_entropy_shadow h
            (2 * n + 1) =
          |spectralProjection h.dominantCoeff| ^ 2

/-- Paper label: `thm:derived-artin-visible-hull-joint-minimality-entropy-obstruction`. The
determinant-active visible hull is already the unique minimal determinant-preserving quotient. Any
further determinant-preserving quotient kernel lies inside that hull, so it cannot kill a hidden
character seen by an active channel. The same dominant channel leaves a nonzero square shadow on
the even and odd subsequences through the existing Chebotarev witness package. -/
theorem paper_derived_artin_visible_hull_joint_minimality_entropy_obstruction
    (h : derived_artin_visible_hull_joint_minimality_entropy_obstruction_data) :
    derived_artin_visible_hull_joint_minimality_entropy_obstruction_statement h := by
  letI := h.joint.instFintypeG
  letI := h.joint.instCommGroupG
  rcases paper_conclusion_artin_determinant_minimal_visible_quotient h.joint with
    ⟨_, hcriterion, hminimal⟩
  rcases paper_kernel_chebotarev_second_main_term_witness h.dominantCoeff h.dominantCoeff_ne_zero
      with ⟨_, hnonzero, hoscillation⟩
  have hle : h.furtherKernel ≤ h.joint.N_det := by
    exact (hcriterion h.furtherKernel).1 h.furtherKernel_preserves_determinant
  have hhidden_notin_ndet : h.dominantHidden ∉ h.joint.N_det := by
    intro hmem
    change ∀ x ∈ h.joint.active, h.joint.channel x h.dominantHidden = 1 at hmem
    exact h.dominantChannel_detects_hidden (hmem h.dominantChannel h.dominantChannel_active)
  have hhidden_notin_further : h.dominantHidden ∉ h.furtherKernel := by
    intro hmem
    exact hhidden_notin_ndet (hle hmem)
  have hshadow_pos : 0 < |spectralProjection h.dominantCoeff| ^ 2 := by
    have habs_pos : 0 < |spectralProjection h.dominantCoeff| := by
      exact abs_pos.mpr hnonzero
    nlinarith
  refine ⟨hminimal, hle, hhidden_notin_further, hshadow_pos, ?_⟩
  intro n
  rcases hoscillation n with ⟨heven, hodd⟩
  constructor
  · unfold derived_artin_visible_hull_joint_minimality_entropy_obstruction_entropy_shadow
    rw [heven]
  · unfold derived_artin_visible_hull_joint_minimality_entropy_obstruction_entropy_shadow
    rw [hodd]

end Omega.DerivedConsequences
