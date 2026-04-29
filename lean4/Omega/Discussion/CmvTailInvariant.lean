import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Discussion

/-- Tail agreement transports the defect index because the input sequence changes only in finitely
many places. -/
lemma discussion_cmv_tail_invariant_tail_defect
    (defectIndex : (ℕ → ℂ) → ℕ) (α αTilde : ℕ → ℂ)
    (hTail : ∃ N0, ∀ n ≥ N0, αTilde n = α n)
    (hDefectTail : ∀ {β γ : ℕ → ℂ},
      (∃ N0, ∀ n ≥ N0, γ n = β n) → defectIndex β = defectIndex γ) :
    defectIndex α = defectIndex αTilde :=
  hDefectTail hTail

/-- Tail agreement likewise transports the point-spectrum residual dimension. -/
lemma discussion_cmv_tail_invariant_tail_point
    (pointSpectrumDim : (ℕ → ℂ) → ℕ) (α αTilde : ℕ → ℂ)
    (hTail : ∃ N0, ∀ n ≥ N0, αTilde n = α n)
    (hPointTail : ∀ {β γ : ℕ → ℂ},
      (∃ N0, ∀ n ≥ N0, γ n = β n) → pointSpectrumDim β = pointSpectrumDim γ) :
    pointSpectrumDim α = pointSpectrumDim αTilde :=
  hPointTail hTail

/-- Eventual equality of Verblunsky tails preserves both the defect index and the point-spectrum
dimension.
    con:discussion-cmv-tail-invariant -/
theorem paper_discussion_cmv_tail_invariant
    (defectIndex pointSpectrumDim : (ℕ → ℂ) → ℕ) (α αTilde : ℕ → ℂ)
    (hTail : ∃ N0, ∀ n ≥ N0, αTilde n = α n)
    (hDefectTail : ∀ {β γ : ℕ → ℂ},
      (∃ N0, ∀ n ≥ N0, γ n = β n) → defectIndex β = defectIndex γ)
    (hPointTail : ∀ {β γ : ℕ → ℂ},
      (∃ N0, ∀ n ≥ N0, γ n = β n) → pointSpectrumDim β = pointSpectrumDim γ) :
    defectIndex α = defectIndex αTilde ∧ pointSpectrumDim α = pointSpectrumDim αTilde := by
  exact ⟨discussion_cmv_tail_invariant_tail_defect defectIndex α αTilde hTail hDefectTail,
    discussion_cmv_tail_invariant_tail_point pointSpectrumDim α αTilde hTail hPointTail⟩

end Omega.Discussion
