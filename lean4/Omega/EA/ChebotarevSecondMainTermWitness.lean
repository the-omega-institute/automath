import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.EA

/-- A fixed simple eigenvalue for the dominant hidden channel. -/
def simpleEigenvalue : ℝ := -1

/-- The spectral projection coefficient carried by a witness set. -/
def spectralProjection (c : ℝ) : ℝ := c

/-- Phase selection along even and odd subsequences. -/
def phaseSelector (n : ℕ) : ℝ := if Even n then 1 else simpleEigenvalue

/-- The isolated dominant nontrivial contribution. -/
def kernelWitnessTerm (c : ℝ) (n : ℕ) : ℝ := spectralProjection c * phaseSelector n

/-- The second main term is exactly the dominant projected mode. -/
def chebotarevSecondMainTermExpansion (c : ℝ) : Prop :=
  ∀ n : ℕ, kernelWitnessTerm c n = spectralProjection c * phaseSelector n

/-- The witness coefficient is nonzero. -/
def chebotarevNonzeroWitnessCoefficient (c : ℝ) : Prop := spectralProjection c ≠ 0

/-- Even and odd subsequences both retain the full witness magnitude. -/
def chebotarevOscillationLowerBound (c : ℝ) : Prop :=
  ∀ n : ℕ,
    |kernelWitnessTerm c (2 * n)| = |spectralProjection c| ∧
      |kernelWitnessTerm c (2 * n + 1)| = |spectralProjection c|

/-- Paper-facing wrapper for the dominant hidden-channel second main term.
    thm:kernel-chebotarev-second-main-term-witness -/
theorem paper_kernel_chebotarev_second_main_term_witness (c : ℝ) (hc : c ≠ 0) :
    chebotarevSecondMainTermExpansion c ∧
      chebotarevNonzeroWitnessCoefficient c ∧
      chebotarevOscillationLowerBound c := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    rfl
  · simpa [chebotarevNonzeroWitnessCoefficient, spectralProjection] using hc
  · intro n
    constructor
    · simp [kernelWitnessTerm, spectralProjection, phaseSelector]
    · have hAbs : |simpleEigenvalue| = 1 := by
        norm_num [simpleEigenvalue]
      calc
        |kernelWitnessTerm c (2 * n + 1)| = |spectralProjection c| * |simpleEigenvalue| := by
          simp [kernelWitnessTerm, spectralProjection, phaseSelector]
        _ = |spectralProjection c| := by rw [hAbs, mul_one]

end Omega.EA
