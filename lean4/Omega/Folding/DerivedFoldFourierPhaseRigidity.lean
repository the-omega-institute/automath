import Mathlib
import Omega.Folding.DerivedAffineReciprocity

open scoped BigOperators

namespace Omega

/-- Paper label: `cor:derived-fold-fourier-phase-rigidity`. The affine reciprocity involution
`r ↦ κ - r` preserves the fold weights and flips the centered sine phase, so the full centered
sine sum cancels termwise. -/
theorem paper_derived_fold_fourier_phase_rigidity (m k : ℕ) (hm : 2 ≤ m) :
    let κ := Nat.fib (m + 1) - 2;
    (Finset.sum (Finset.range (κ + 1)) fun r =>
      (weightCongruenceCount m r : ℝ) *
        Real.sin (2 * Real.pi * (k : ℝ) * ((r : ℝ) - (κ : ℝ) / 2) / (Nat.fib (m + 2) : ℝ))) = 0 := by
  dsimp
  let κ := Nat.fib (m + 1) - 2
  let f : ℕ → ℝ := fun r =>
    (weightCongruenceCount m r : ℝ) *
      Real.sin (2 * Real.pi * (k : ℝ) * ((r : ℝ) - (κ : ℝ) / 2) / (Nat.fib (m + 2) : ℝ))
  have hpair : ∀ r ∈ Finset.range (κ + 1), f (κ - r) = -f r := by
    intro r hr
    have hrle : r ≤ κ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
    dsimp [f]
    rw [paper_derived_fold_affine_reciprocity m r hm hrle]
    have hcentered :
        (((κ - r : ℕ) : ℝ) - (κ : ℝ) / 2) = -((r : ℝ) - (κ : ℝ) / 2) := by
      rw [Nat.cast_sub hrle]
      ring
    have hphase :
        2 * Real.pi * (k : ℝ) * ((((κ - r : ℕ) : ℝ) - (κ : ℝ) / 2)) / (Nat.fib (m + 2) : ℝ) =
          -(2 * Real.pi * (k : ℝ) * (((r : ℝ) - (κ : ℝ) / 2)) / (Nat.fib (m + 2) : ℝ)) := by
      rw [hcentered]
      ring
    rw [hphase, Real.sin_neg]
    ring
  have hreflect :
      Finset.sum (Finset.range (κ + 1)) (fun r => f (κ - r)) =
        Finset.sum (Finset.range (κ + 1)) f := by
    simpa [Nat.succ_eq_add_one, Nat.add_sub_cancel] using (Finset.sum_range_reflect f (κ + 1))
  have hsum_eq_neg :
      Finset.sum (Finset.range (κ + 1)) f = -Finset.sum (Finset.range (κ + 1)) f := by
    calc
      Finset.sum (Finset.range (κ + 1)) f = Finset.sum (Finset.range (κ + 1)) (fun r => f (κ - r)) :=
        hreflect.symm
      _ = Finset.sum (Finset.range (κ + 1)) (fun r => -f r) := by
        refine Finset.sum_congr rfl ?_
        intro r hr
        exact hpair r hr
      _ = -Finset.sum (Finset.range (κ + 1)) f := by
        rw [Finset.sum_neg_distrib]
  have hzero : Finset.sum (Finset.range (κ + 1)) f = 0 := by
    linarith
  simpa [f, κ] using hzero

end Omega
