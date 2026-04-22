import Omega.TypedAddressBiaxialCompletion.ComovingUniformMinimization
import Omega.TypedAddressBiaxialCompletion.JensenCountableCriterion

namespace Omega.CircleDimension

open Filter
open Omega.TypedAddressBiaxialCompletion
open Omega.TypedAddressBiaxialCompletion.JensenCountableCriterionData

/-- Chapter-facing notation for the uniform comoving defect certificate carried by a cofinal
radius sequence. -/
def uniformComovingDefectCriterion (defect : ℝ → ℝ) (rhoSeq : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, defect (rhoSeq n) = 0

/-- Chapter-facing translation of the typed-address countable Jensen criterion.
    thm:cdim-rh-iff-uniform-comoving-defect -/
theorem paper_cdim_rh_iff_uniform_comoving_defect
    (defect : ℝ → ℝ) (zeroFree : ℝ → Prop)
    (semantics :
      ∀ rho : ℝ, 0 < rho → rho < 1 → 0 ≤ defect rho ∧ (defect rho = 0 ↔ zeroFree rho))
    (defect_monotone :
      ∀ {ρ₁ ρ₂ : ℝ}, 0 < ρ₁ → ρ₂ < 1 → ρ₁ ≤ ρ₂ → defect ρ₁ ≤ defect ρ₂)
    (rhoSeq : ℕ → ℝ) (rhoSeq_mono : Monotone rhoSeq)
    (rhoSeq_mem : ∀ n : ℕ, 0 < rhoSeq n ∧ rhoSeq n < 1)
    (rhoSeq_tendsto : Tendsto rhoSeq atTop (nhds 1))
    (rhoSeq_covers : ∀ {ρ : ℝ}, 0 < ρ → ρ < 1 → ∃ n : ℕ, ρ ≤ rhoSeq n) :
    (∀ {ρ : ℝ}, 0 < ρ → ρ < 1 → zeroFree ρ) ↔
      uniformComovingDefectCriterion defect rhoSeq := by
  let D : JensenCountableCriterionData :=
    { defect := defect
      zeroFree := zeroFree
      semantics := semantics
      defect_monotone := @defect_monotone
      rhoSeq := rhoSeq
      rhoSeq_mono := rhoSeq_mono
      rhoSeq_mem := rhoSeq_mem
      rhoSeq_tendsto := rhoSeq_tendsto
      rhoSeq_covers := @rhoSeq_covers }
  simpa [uniformComovingDefectCriterion, JensenCountableCriterionData.rh] using
    paper_app_jensen_countable_criterion D

end Omega.CircleDimension
