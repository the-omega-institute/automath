import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace Omega.Zeta

/--
Concrete public-coin protocol data for a finite Hankel-singularity HVZK abstraction.
The finite sets record the obstruction, extracting challenge pairs, and transcript support.
-/
structure xi_hankel_singularity_hvzk_data where
  Instance : Type*
  Challenge : Type*
  Transcript : Type*
  witness : Instance → Prop
  obstructionChallenges : Instance → Finset Challenge
  failedChallenges : Instance → Finset Challenge
  acceptingPairs : Instance → Finset (Challenge × Challenge)
  extractingPairs : Instance → Finset (Challenge × Challenge)
  transcriptSupport : Instance → Finset Transcript
  realTranscriptWeight : Instance → Transcript → ℕ
  simulatedTranscriptWeight : Instance → Transcript → ℕ
  failed_subset_obstruction :
    ∀ x : Instance, failedChallenges x ⊆ obstructionChallenges x
  accepting_subset_extracting :
    ∀ x : Instance, acceptingPairs x ⊆ extractingPairs x
  real_eq_simulated_on_support :
    ∀ (x : Instance) (t : Transcript),
      t ∈ transcriptSupport x → realTranscriptWeight x t = simulatedTranscriptWeight x t
  real_zero_off_support :
    ∀ (x : Instance) (t : Transcript), t ∉ transcriptSupport x → realTranscriptWeight x t = 0
  simulated_zero_off_support :
    ∀ (x : Instance) (t : Transcript),
      t ∉ transcriptSupport x → simulatedTranscriptWeight x t = 0

/-- Completeness failure is bounded by the kernel obstruction count. -/
def xi_hankel_singularity_hvzk_data.completeness_bound
    (D : xi_hankel_singularity_hvzk_data) : Prop :=
  ∀ x : D.Instance,
    D.witness x → (D.failedChallenges x).card ≤ (D.obstructionChallenges x).card

/-- Two accepting challenges can only occur inside the extracting-pair obstruction set. -/
def xi_hankel_singularity_hvzk_data.soundness_bound
    (D : xi_hankel_singularity_hvzk_data) : Prop :=
  ∀ x : D.Instance, (D.acceptingPairs x).card ≤ (D.extractingPairs x).card

/-- The simulator transcript distribution agrees pointwise with the real distribution. -/
def xi_hankel_singularity_hvzk_data.perfect_zero_knowledge
    (D : xi_hankel_singularity_hvzk_data) : Prop :=
  ∀ (x : D.Instance) (t : D.Transcript),
    D.realTranscriptWeight x t = D.simulatedTranscriptWeight x t

/-- Paper label: `thm:xi-hankel-singularity-hvzk`. -/
theorem paper_xi_hankel_singularity_hvzk (D : xi_hankel_singularity_hvzk_data) :
    D.completeness_bound ∧ D.soundness_bound ∧ D.perfect_zero_knowledge := by
  have hcomplete : D.completeness_bound := by
    intro x _hx
    exact Finset.card_le_card (D.failed_subset_obstruction x)
  have hsound : D.soundness_bound := by
    intro x
    exact Finset.card_le_card (D.accepting_subset_extracting x)
  have hzk : D.perfect_zero_knowledge := by
    intro x t
    by_cases ht : t ∈ D.transcriptSupport x
    · exact D.real_eq_simulated_on_support x t ht
    · rw [D.real_zero_off_support x t ht, D.simulated_zero_off_support x t ht]
  exact ⟨hcomplete, hsound, hzk⟩

end Omega.Zeta
