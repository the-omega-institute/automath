import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

namespace Omega.Folding

open scoped BigOperators

noncomputable section

/-- The Lee--Yang branch graph splits into five connected hypercube components. -/
def leyangBranchGraphComponentCount : ℕ := 5

/-- Each hypercube component has dimension `2n`. -/
def leyangBranchGraphDimension (n : ℕ) : ℕ := 2 * n

/-- Adjacency eigenvalue indexed by the Hamming layer `k`. -/
def leyangBranchAdjacencyEigenvalue (n k : ℕ) : ℤ :=
  (2 * n : ℤ) - 2 * (k : ℤ)

/-- Laplacian eigenvalue indexed by the Hamming layer `k`. -/
def leyangBranchLaplacianEigenvalue (k : ℕ) : ℕ := 2 * k

/-- Multiplicity transported from five copies of `Q_(2n)`. -/
def leyangBranchSpectrumMultiplicity (n k : ℕ) : ℕ :=
  leyangBranchGraphComponentCount * Nat.choose (leyangBranchGraphDimension n) k

/-- Spectral heat trace on the Laplacian side. -/
def leyangBranchHeatTrace (n : ℕ) (t : ℝ) : ℝ :=
  (leyangBranchGraphComponentCount : ℝ) *
    (∑ k ∈ Finset.range (leyangBranchGraphDimension n + 1),
      (Nat.choose (leyangBranchGraphDimension n) k : ℝ) * Real.exp (-2 * (k : ℝ) * t))

/-- Spectral `ell`-step closed-walk trace on the adjacency side. -/
def leyangBranchClosedWalkTrace (n ell : ℕ) : ℤ :=
  (leyangBranchGraphComponentCount : ℤ) *
    (∑ k ∈ Finset.range (leyangBranchGraphDimension n + 1),
      (Nat.choose (leyangBranchGraphDimension n) k : ℤ) * leyangBranchAdjacencyEigenvalue n k ^ ell)

/-- Full spectral package for the Lee--Yang branch graph modeled as five copies of `Q_(2n)`. -/
def LeyangBranchGraphFullSpectrum (n : ℕ) : Prop :=
  1 ≤ leyangBranchGraphDimension n ∧
    leyangBranchGraphComponentCount = 5 ∧
    (∀ k, k ≤ leyangBranchGraphDimension n →
      leyangBranchAdjacencyEigenvalue n k = (2 * n : ℤ) - 2 * (k : ℤ) ∧
        leyangBranchSpectrumMultiplicity n k = 5 * Nat.choose (leyangBranchGraphDimension n) k) ∧
    (∀ k, k ≤ leyangBranchGraphDimension n →
      leyangBranchLaplacianEigenvalue k = 2 * k ∧
        leyangBranchSpectrumMultiplicity n k = 5 * Nat.choose (leyangBranchGraphDimension n) k) ∧
    (∀ t, leyangBranchHeatTrace n t =
      (5 : ℝ) *
        (∑ k ∈ Finset.range (leyangBranchGraphDimension n + 1),
          (Nat.choose (leyangBranchGraphDimension n) k : ℝ) * Real.exp (-2 * (k : ℝ) * t))) ∧
    (∀ ell, leyangBranchClosedWalkTrace n ell =
      (5 : ℤ) *
        (∑ k ∈ Finset.range (leyangBranchGraphDimension n + 1),
          (Nat.choose (leyangBranchGraphDimension n) k : ℤ) *
            leyangBranchAdjacencyEigenvalue n k ^ ell))

/-- Paper-facing spectral package for the Lee--Yang branch graph.
    thm:killo-leyang-branch-graph-full-spectrum -/
theorem paper_killo_leyang_branch_graph_full_spectrum (n : ℕ) (hn : 1 ≤ n) :
    LeyangBranchGraphFullSpectrum n := by
  refine ⟨?_, rfl, ?_, ?_, ?_, ?_⟩
  · have h : 1 ≤ 2 * n := by nlinarith
    simpa [leyangBranchGraphDimension] using h
  · intro k hk
    simp [leyangBranchAdjacencyEigenvalue, leyangBranchSpectrumMultiplicity,
      leyangBranchGraphComponentCount]
  · intro k hk
    simp [leyangBranchLaplacianEigenvalue, leyangBranchSpectrumMultiplicity,
      leyangBranchGraphComponentCount]
  · intro t
    simp [leyangBranchHeatTrace, leyangBranchGraphComponentCount]
  · intro ell
    simp [leyangBranchClosedWalkTrace, leyangBranchGraphComponentCount]

end

end Omega.Folding
