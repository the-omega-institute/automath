import Mathlib.Tactic
import Omega.POM.FiberReconstructionRadiusCenterAntipodes

namespace Omega.Folding

open Omega.POM

/-- Deterministic single-pass counter for the fold fiber radius budget. -/
def foldFiberRMaxScan (lengths : List ℕ) : ℕ :=
  lengths.foldl (fun acc ℓ => acc + fibPathRadius ℓ) 0

/-- The no-gap rewrite spectrum attached to a path-component decomposition. -/
def foldFiberRewriteSpectrum (lengths : List ℕ) : Finset ℕ :=
  Finset.range (fiberReconstructionRadius lengths + 1)

/-- Fiber level membership in the no-gap rewrite spectrum. -/
def FoldFiberLevel (lengths : List ℕ) (k : ℕ) : Prop :=
  k ∈ foldFiberRewriteSpectrum lengths

private lemma foldFiberRMaxScan_eq_radiusAux (lengths : List ℕ) (acc : ℕ) :
    lengths.foldl (fun s ℓ => s + fibPathRadius ℓ) acc = acc + fiberReconstructionRadius lengths := by
  induction lengths generalizing acc with
  | nil =>
      simp [fiberReconstructionRadius]
  | cons ℓ lengths ih =>
      simp [List.foldl, fiberReconstructionRadius, ih, add_assoc]

lemma foldFiberRMaxScan_eq_radius (lengths : List ℕ) :
    foldFiberRMaxScan lengths = fiberReconstructionRadius lengths := by
  simpa [foldFiberRMaxScan] using foldFiberRMaxScan_eq_radiusAux lengths 0

lemma foldFiberRewriteSpectrum_noGaps (lengths : List ℕ) (k : ℕ) :
    FoldFiberLevel lengths k ↔ k ≤ fiberReconstructionRadius lengths := by
  simp [FoldFiberLevel, foldFiberRewriteSpectrum]

/-- Paper-facing logspace wrapper for fold-fiber level membership: the no-gap rewrite spectrum is
exactly the interval `0 .. R_max`, and `R_max` is computed by a single scan over the path lengths.
    thm:fold-fiber-level-logspace -/
theorem paper_fold_fiber_level_logspace (lengths : List ℕ) (k : ℕ) :
    FoldFiberLevel lengths k ↔ 0 ≤ k ∧ k ≤ foldFiberRMaxScan lengths := by
  rw [foldFiberRewriteSpectrum_noGaps, foldFiberRMaxScan_eq_radius]
  constructor
  · intro hk
    exact ⟨Nat.zero_le _, hk⟩
  · intro hk
    exact hk.2

end Omega.Folding
