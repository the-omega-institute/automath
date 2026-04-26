import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.POM.MicrocanonicalFoldClassCount
import Omega.POM.ObliviousWidthSBranchingProgramCount

namespace Omega.POM

open scoped BigOperators

/-- Concrete data for the microcanonical streaming-program rarity estimate. The branching-program
count controls the total number of realizable functions, while the entropy lower bound packages the
microcanonical class-size growth on the exponential scale. -/
structure PomMicrocanonicalStreamingProgramRarityData where
  X : Type
  instFintypeX : Fintype X
  instDecidableEqX : DecidableEq X
  fiberProfile : X → ℕ
  layers : ℕ
  width : ℕ
  outputAlphabet : ℕ
  entropyLowerBound : ℝ
  width_pos : 1 ≤ width
  outputAlphabet_pos : 1 ≤ outputAlphabet
  paper_label_pom_microcanonical_streaming_program_rarity_entropy_bound :
    Real.exp entropyLowerBound ≤ (microcanonicalFoldClassCount fiberProfile : ℝ)

attribute [instance] PomMicrocanonicalStreamingProgramRarityData.instFintypeX
attribute [instance] PomMicrocanonicalStreamingProgramRarityData.instDecidableEqX

namespace PomMicrocanonicalStreamingProgramRarityData

def classCard (D : PomMicrocanonicalStreamingProgramRarityData) : ℕ :=
  microcanonicalFoldClassCount D.fiberProfile

def programCount (D : PomMicrocanonicalStreamingProgramRarityData) : ℕ :=
  obliviousWidthSFunctionCount D.layers D.width D.outputAlphabet

def programBoundNat (D : PomMicrocanonicalStreamingProgramRarityData) : ℕ :=
  D.outputAlphabet ^ D.width * D.width ^ (2 * D.width * D.layers)

noncomputable def programBoundReal (D : PomMicrocanonicalStreamingProgramRarityData) : ℝ :=
  (D.outputAlphabet : ℝ) ^ D.width * (D.width : ℝ) ^ (2 * D.width * D.layers)

def intersectionCount (D : PomMicrocanonicalStreamingProgramRarityData) : ℕ :=
  Nat.min D.classCard D.programCount

noncomputable def rarityRatio (D : PomMicrocanonicalStreamingProgramRarityData) : ℝ :=
  (D.intersectionCount : ℝ) / (D.classCard : ℝ)

/-- The realized microcanonical fraction is bounded first by the branching-program counting bound
divided by the class size, and then by the exponential entropy corollary. -/
def streamingProgramRare (D : PomMicrocanonicalStreamingProgramRarityData) : Prop :=
  D.intersectionCount ≤ D.classCard ∧
    D.intersectionCount ≤ D.programCount ∧
    D.rarityRatio ≤ D.programBoundReal / Real.exp D.entropyLowerBound ∧
    D.programBoundReal / Real.exp D.entropyLowerBound =
      Real.exp (Real.log D.programBoundReal - D.entropyLowerBound)

end PomMicrocanonicalStreamingProgramRarityData

open PomMicrocanonicalStreamingProgramRarityData

/-- Paper label: `thm:pom-microcanonical-streaming-program-rarity`. Intersect the branching-program
class with the microcanonical class, divide the counting bound by the class size, and use the
entropy lower bound to package the resulting rarity estimate in exponential form. -/
theorem paper_pom_microcanonical_streaming_program_rarity
    (D : PomMicrocanonicalStreamingProgramRarityData) : D.streamingProgramRare := by
  have hinter_class : D.intersectionCount ≤ D.classCard := Nat.min_le_left _ _
  have hinter_program : D.intersectionCount ≤ D.programCount := Nat.min_le_right _ _
  have hprogram_bound_nat : D.programCount ≤ D.programBoundNat := by
    simpa [PomMicrocanonicalStreamingProgramRarityData.programCount,
      PomMicrocanonicalStreamingProgramRarityData.programBoundNat] using
      paper_pom_oblivious_widthS_branching_program_count D.layers D.width D.outputAlphabet
  have hprogram_bound_real_nat :
      (D.programCount : ℝ) ≤ (D.programBoundNat : ℝ) := by
    exact_mod_cast hprogram_bound_nat
  have hbound_cast :
      (D.programBoundNat : ℝ) = D.programBoundReal := by
    simp [PomMicrocanonicalStreamingProgramRarityData.programBoundNat,
      PomMicrocanonicalStreamingProgramRarityData.programBoundReal]
  have hprogram_bound_real :
      (D.programCount : ℝ) ≤ D.programBoundReal := by
    simpa [hbound_cast] using hprogram_bound_real_nat
  have hexp_pos : 0 < Real.exp D.entropyLowerBound := Real.exp_pos _
  have hclass_pos : 0 < (D.classCard : ℝ) := by
    have hclass_ge :
        Real.exp D.entropyLowerBound ≤ (D.classCard : ℝ) := by
      simpa [PomMicrocanonicalStreamingProgramRarityData.classCard] using
        D.paper_label_pom_microcanonical_streaming_program_rarity_entropy_bound
    exact lt_of_lt_of_le hexp_pos hclass_ge
  have hratio_le_program :
      D.rarityRatio ≤ (D.programCount : ℝ) / (D.classCard : ℝ) := by
    dsimp [PomMicrocanonicalStreamingProgramRarityData.rarityRatio]
    exact div_le_div_of_nonneg_right
      (show (D.intersectionCount : ℝ) ≤ (D.programCount : ℝ) by exact_mod_cast hinter_program)
      (le_of_lt hclass_pos)
  have hprogram_div_le :
      (D.programCount : ℝ) / (D.classCard : ℝ) ≤ D.programBoundReal / (D.classCard : ℝ) := by
    exact div_le_div_of_nonneg_right hprogram_bound_real (le_of_lt hclass_pos)
  have hbound_nonneg : 0 ≤ D.programBoundReal := by
    dsimp [PomMicrocanonicalStreamingProgramRarityData.programBoundReal]
    positivity
  have hclass_ge :
      Real.exp D.entropyLowerBound ≤ (D.classCard : ℝ) := by
    simpa [PomMicrocanonicalStreamingProgramRarityData.classCard] using
      D.paper_label_pom_microcanonical_streaming_program_rarity_entropy_bound
  have hclass_div_le :
      D.programBoundReal / (D.classCard : ℝ) ≤
        D.programBoundReal / Real.exp D.entropyLowerBound := by
    exact div_le_div_of_nonneg_left hbound_nonneg hexp_pos hclass_ge
  have hprogram_bound_pos : 0 < D.programBoundReal := by
    have hout : 0 < (D.outputAlphabet : ℝ) := by
      exact_mod_cast lt_of_lt_of_le (by norm_num : 0 < 1) D.outputAlphabet_pos
    have hwidth : 0 < (D.width : ℝ) := by
      exact_mod_cast lt_of_lt_of_le (by norm_num : 0 < 1) D.width_pos
    dsimp [PomMicrocanonicalStreamingProgramRarityData.programBoundReal]
    exact mul_pos (pow_pos hout _) (pow_pos hwidth _)
  have hratio_bound :
      D.rarityRatio ≤ D.programBoundReal / Real.exp D.entropyLowerBound := by
    exact le_trans hratio_le_program (le_trans hprogram_div_le hclass_div_le)
  have hexponential_form :
      D.programBoundReal / Real.exp D.entropyLowerBound =
        Real.exp (Real.log D.programBoundReal - D.entropyLowerBound) := by
    calc
      D.programBoundReal / Real.exp D.entropyLowerBound =
          Real.exp (Real.log D.programBoundReal) / Real.exp D.entropyLowerBound := by
            rw [Real.exp_log hprogram_bound_pos]
      _ = Real.exp (Real.log D.programBoundReal - D.entropyLowerBound) := by
            rw [Real.exp_sub]
  exact ⟨hinter_class, hinter_program, hratio_bound, hexponential_form⟩

end Omega.POM
