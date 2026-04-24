import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

/-- Concrete package for the affine-in-`u` splitting `B(u) = B₀ + u B₁` together with the
conjugation action induced by `Π⁻¹(·)Π`. In this scalar wrapper, the action is represented by a
map `Pi` which is additive, rational-linear, and exchanges `B₀` with `B₁`. -/
structure SyncKernelEvenOddSplittingData where
  B0 : ℚ
  B1 : ℚ
  Pi : ℚ → ℚ
  sync_kernel_even_odd_splitting_pi_add : ∀ x y : ℚ, Pi (x + y) = Pi x + Pi y
  sync_kernel_even_odd_splitting_pi_rat : ∀ q x : ℚ, Pi (q * x) = q * Pi x
  sync_kernel_even_odd_splitting_pi_B0 : Pi B0 = B1
  sync_kernel_even_odd_splitting_pi_B1 : Pi B1 = B0

/-- The affine block `B(u) = B₀ + u B₁`. -/
def sync_kernel_even_odd_splitting_B (D : SyncKernelEvenOddSplittingData) (u : ℚ) : ℚ :=
  D.B0 + u * D.B1

/-- The `Π`-even part `(B₀ + B₁)/2`. -/
def sync_kernel_even_odd_splitting_Bsym (D : SyncKernelEvenOddSplittingData) : ℚ :=
  (1 / 2 : ℚ) * (D.B0 + D.B1)

/-- The `Π`-odd part `(B₁ - B₀)/2`. -/
def sync_kernel_even_odd_splitting_Basym (D : SyncKernelEvenOddSplittingData) : ℚ :=
  (1 / 2 : ℚ) * (D.B1 - D.B0)

namespace SyncKernelEvenOddSplittingData

/-- Direct expansion of `B(u)` into its `Π`-even and `Π`-odd parts. -/
def splitFormula (D : SyncKernelEvenOddSplittingData) : Prop :=
  ∀ u : ℚ,
    sync_kernel_even_odd_splitting_B D u =
      (1 + u) * sync_kernel_even_odd_splitting_Bsym D +
        (u - 1) * sync_kernel_even_odd_splitting_Basym D

/-- The conjugation action fixes the `Π`-even part and negates the `Π`-odd part. -/
def piParityFormula (D : SyncKernelEvenOddSplittingData) : Prop :=
  D.Pi (sync_kernel_even_odd_splitting_Bsym D) = sync_kernel_even_odd_splitting_Bsym D ∧
    D.Pi (sync_kernel_even_odd_splitting_Basym D) = -sync_kernel_even_odd_splitting_Basym D

/-- Uniqueness of the affine decomposition in the basis `1 + u`, `u - 1`. -/
def uniqueSplitFormula (D : SyncKernelEvenOddSplittingData) : Prop :=
  ∀ S A : ℚ,
    (∀ u : ℚ,
      sync_kernel_even_odd_splitting_B D u = (1 + u) * S + (u - 1) * A) →
        S = sync_kernel_even_odd_splitting_Bsym D ∧ A = sync_kernel_even_odd_splitting_Basym D

end SyncKernelEvenOddSplittingData

open SyncKernelEvenOddSplittingData

/-- Paper label: `lem:sync-kernel-even-odd-splitting`. The affine kernel block splits uniquely
into its `Π`-even and `Π`-odd components, and the conjugation action exchanges the odd part by a
sign. -/
theorem paper_sync_kernel_even_odd_splitting (D : SyncKernelEvenOddSplittingData) :
    D.splitFormula ∧ D.piParityFormula ∧ D.uniqueSplitFormula := by
  refine ⟨?_, ?_, ?_⟩
  · intro u
    unfold sync_kernel_even_odd_splitting_B sync_kernel_even_odd_splitting_Bsym
      sync_kernel_even_odd_splitting_Basym
    ring
  · constructor
    · calc
        D.Pi (sync_kernel_even_odd_splitting_Bsym D)
            = D.Pi ((1 / 2 : ℚ) * D.B0 + (1 / 2 : ℚ) * D.B1) := by
                unfold sync_kernel_even_odd_splitting_Bsym
                ring
        _ = (1 / 2 : ℚ) * D.Pi D.B0 + (1 / 2 : ℚ) * D.Pi D.B1 := by
              rw [D.sync_kernel_even_odd_splitting_pi_add, D.sync_kernel_even_odd_splitting_pi_rat,
                D.sync_kernel_even_odd_splitting_pi_rat]
        _ = (1 / 2 : ℚ) * D.B1 + (1 / 2 : ℚ) * D.B0 := by
              rw [D.sync_kernel_even_odd_splitting_pi_B0, D.sync_kernel_even_odd_splitting_pi_B1]
        _ = sync_kernel_even_odd_splitting_Bsym D := by
              unfold sync_kernel_even_odd_splitting_Bsym
              ring
    · calc
        D.Pi (sync_kernel_even_odd_splitting_Basym D)
            = D.Pi ((1 / 2 : ℚ) * D.B1 + (-1 / 2 : ℚ) * D.B0) := by
                unfold sync_kernel_even_odd_splitting_Basym
                ring
        _ = (1 / 2 : ℚ) * D.Pi D.B1 + (-1 / 2 : ℚ) * D.Pi D.B0 := by
              rw [D.sync_kernel_even_odd_splitting_pi_add, D.sync_kernel_even_odd_splitting_pi_rat,
                D.sync_kernel_even_odd_splitting_pi_rat]
        _ = (1 / 2 : ℚ) * D.B0 + (-1 / 2 : ℚ) * D.B1 := by
              rw [D.sync_kernel_even_odd_splitting_pi_B1, D.sync_kernel_even_odd_splitting_pi_B0]
        _ = -sync_kernel_even_odd_splitting_Basym D := by
              unfold sync_kernel_even_odd_splitting_Basym
              ring
  · intro S A hsplit
    have h0 : D.B0 = S - A := by
      simpa [sync_kernel_even_odd_splitting_B, sub_eq_add_neg] using hsplit 0
    have h1 : D.B0 + D.B1 = 2 * S := by
      have h1' := hsplit 1
      have h1'' : D.B0 + D.B1 = (1 + 1 : ℚ) * S := by
        simpa [sync_kernel_even_odd_splitting_B] using h1'
      linarith
    have hS : S = sync_kernel_even_odd_splitting_Bsym D := by
      unfold sync_kernel_even_odd_splitting_Bsym
      linarith
    have hA : A = sync_kernel_even_odd_splitting_Basym D := by
      unfold sync_kernel_even_odd_splitting_Basym
      linarith [h0, hS]
    exact ⟨hS, hA⟩

end Omega.SyncKernelWeighted
