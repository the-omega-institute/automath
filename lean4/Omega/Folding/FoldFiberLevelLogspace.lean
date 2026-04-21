import Mathlib.Tactic
import Omega.POM.FiberReconstructionRadiusCenterAntipodes
import Omega.POM.PathIndSetPolyClosed

namespace Omega.Folding

open Omega.POM

/-- Product decomposition of the fold-fiber generating polynomial `Z_x(t)`. -/
noncomputable def foldFiberCountPolynomial : List ℕ → Polynomial ℤ
  | [] => 1
  | ℓ :: lengths => Omega.pathIndSetPoly ℓ * foldFiberCountPolynomial lengths

/-- Total fold-fiber count obtained by evaluating each path factor at `t = 1`. -/
def foldFiberTotalCount : List ℕ → ℕ
  | [] => 1
  | ℓ :: lengths => Nat.fib (ℓ + 2) * foldFiberTotalCount lengths

/-- Layered fold-fiber count computed by the bounded-degree convolution DP for product
decompositions. -/
noncomputable def foldFiberLayerCount : List ℕ → ℕ → ℤ
  | [], 0 => 1
  | [], _ + 1 => 0
  | ℓ :: lengths, k =>
      ∑ x ∈ Finset.antidiagonal k,
        (Omega.pathIndSetPoly ℓ).coeff x.1 * foldFiberLayerCount lengths x.2

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

/-- The Fibonacci values multiply across the path decomposition. -/
lemma foldFiberTotalCount_eq_prod (lengths : List ℕ) :
    foldFiberTotalCount lengths = (lengths.map fun ℓ => Nat.fib (ℓ + 2)).prod := by
  induction lengths with
  | nil =>
      simp [foldFiberTotalCount]
  | cons ℓ lengths ih =>
      simp [foldFiberTotalCount, ih]

/-- Evaluating the product polynomial at `t = 1` yields the total fiber count. -/
lemma foldFiberCountPolynomial_eval_one (lengths : List ℕ) :
    (foldFiberCountPolynomial lengths).eval 1 = (foldFiberTotalCount lengths : ℤ) := by
  induction lengths with
  | nil =>
      simp [foldFiberCountPolynomial, foldFiberTotalCount]
  | cons ℓ lengths ih =>
      simp [foldFiberCountPolynomial, foldFiberTotalCount, ih, Omega.pathIndSetPoly_eval_one,
        Nat.cast_mul]

/-- The coefficient DP computes exactly the coefficients of the product generating polynomial. -/
lemma foldFiberLayerCount_eq_coeff (lengths : List ℕ) (k : ℕ) :
    foldFiberLayerCount lengths k = (foldFiberCountPolynomial lengths).coeff k := by
  induction lengths generalizing k with
  | nil =>
      cases k with
      | zero =>
          simp [foldFiberLayerCount, foldFiberCountPolynomial]
      | succ k =>
          simp [foldFiberLayerCount, foldFiberCountPolynomial, Polynomial.coeff_one]
  | cons ℓ lengths ih =>
      simp [foldFiberLayerCount, foldFiberCountPolynomial, Polynomial.coeff_mul, ih]

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

/-- Paper-facing logspace wrapper for total and layered fold-fiber counts: the same path-component
scan that exposes `Z_x(t)` as a product of path polynomials yields the total count by evaluation at
`t = 1`, while the layered counts are recovered by bounded-degree coefficient DP on the same
product.
    thm:fold-fiber-counts-logspace -/
theorem paper_fold_fiber_counts_logspace (lengths : List ℕ) :
    foldFiberTotalCount lengths = (lengths.map fun ℓ => Nat.fib (ℓ + 2)).prod ∧
      (foldFiberCountPolynomial lengths).eval 1 = (foldFiberTotalCount lengths : ℤ) ∧
      ∀ k : ℕ, foldFiberLayerCount lengths k = (foldFiberCountPolynomial lengths).coeff k := by
  refine ⟨foldFiberTotalCount_eq_prod lengths, foldFiberCountPolynomial_eval_one lengths, ?_⟩
  intro k
  exact foldFiberLayerCount_eq_coeff lengths k

end Omega.Folding
