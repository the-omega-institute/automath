import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.GroupUnification

/-- Reindexing by an involution preserves the counting inner product sum.
    prop:window6-chiral-orthogonality-to-type-observables -/
theorem involutive_sum_reindex
    {α : Type*} [Fintype α] [DecidableEq α]
    (σ : α → α) (hσ : Function.Involutive σ) (h : α → ℝ) :
    (∑ x, h x) = ∑ x, h (σ x) := by
  simpa using
    (Fintype.sum_bijective σ hσ.bijective (fun x => h (σ x)) h (fun _ => rfl)).symm

/-- Invariant observables are orthogonal to anti-invariant ones under the counting
    inner product of a finite involution.
    prop:window6-chiral-orthogonality-to-type-observables -/
theorem involutive_invariant_antiInvariant_orthogonal
    {α : Type*} [Fintype α] [DecidableEq α]
    (σ : α → α) (hσ : Function.Involutive σ)
    (g f : α → ℝ)
    (hg : ∀ x, g (σ x) = g x)
    (hf : ∀ x, f (σ x) = -f x) :
    (∑ x, g x * f x) = 0 := by
  have hreindex :
      (∑ x, g x * f x) = ∑ x, g (σ x) * f (σ x) :=
    involutive_sum_reindex σ hσ (fun x => g x * f x)
  have hneg :
      (∑ x, g x * f x) = -∑ x, g x * f x := by
    calc
      (∑ x, g x * f x) = ∑ x, g (σ x) * f (σ x) := hreindex
      _ = ∑ x, -(g x * f x) := by
        congr with x
        rw [hg x, hf x]
        ring
      _ = -∑ x, g x * f x := by
        rw [Finset.sum_neg_distrib]
  linarith

/-- Paper seed for chiral orthogonality: if a type observable is invariant under
    the geometric involution and a chiral observable is anti-invariant, then their
    counting inner product vanishes.
    prop:window6-chiral-orthogonality-to-type-observables -/
theorem paper_window6_chiral_orthogonality_type_observables_seeds
    {α : Type*} [Fintype α] [DecidableEq α]
    (σ : α → α) (hσ : Function.Involutive σ)
    (g f : α → ℝ)
    (hg : ∀ x, g (σ x) = g x)
    (hf : ∀ x, f (σ x) = -f x) :
    (∑ x, g x * f x) = 0 :=
  involutive_invariant_antiInvariant_orthogonal σ hσ g f hg hf

end Omega.GroupUnification
