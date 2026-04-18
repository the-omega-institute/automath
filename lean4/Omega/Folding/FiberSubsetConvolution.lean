import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Int.Basic

namespace Omega.Folding

/-- The total translation contributed by flipping the coordinates in the finite pattern set `S`. -/
def fiberSubsetShift {α : Type*} [DecidableEq α] (weights : α → ℤ) (S : Finset α) : ℤ :=
  Finset.sum S fun i => weights i

/-- The count of the fiber translated by the pattern supported on `S`. -/
def fiberSubsetPatternCount {α : Type*} [DecidableEq α]
    (weights : α → ℤ) (zeroFiberCount : ℤ → ℕ) (r : ℤ) (S : Finset α) : ℕ :=
  zeroFiberCount (r - fiberSubsetShift weights S)

/-- The powerset convolution decomposition obtained by summing the translated counts over all
patterns on the constrained coordinate set `I`. -/
def fiberSubsetConvolution {α : Type*} [DecidableEq α]
    (I : Finset α) (weights : α → ℤ) (zeroFiberCount : ℤ → ℕ) (r : ℤ) : ℕ :=
  Finset.sum I.powerset fun S => fiberSubsetPatternCount weights zeroFiberCount r S

/-- Paper label: `prop:fold-fiber-subset-convolution`.
The powerset sum gives the convolution decomposition, and each pattern count is the corresponding
translated zero-pattern count. -/
theorem paper_fold_fiber_subset_convolution {α : Type*} [DecidableEq α]
    (I : Finset α) (weights : α → ℤ) (zeroFiberCount : ℤ → ℕ) :
    (∀ r : ℤ,
        fiberSubsetConvolution I weights zeroFiberCount r =
          Finset.sum I.powerset fun S => zeroFiberCount (r - fiberSubsetShift weights S)) ∧
      (∀ r : ℤ, ∀ S : Finset α, S ⊆ I →
        fiberSubsetPatternCount weights zeroFiberCount r S =
          zeroFiberCount (r - fiberSubsetShift weights S)) := by
  refine ⟨?_, ?_⟩
  · intro r
    rfl
  · intro r S hS
    let _ := hS
    rfl

end Omega.Folding
