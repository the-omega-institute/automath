import Mathlib.Tactic
import Omega.Graph.TransferMatrix

/-! # Frobenius–Perron dimension of the golden mean adjacency matrix

This file proves that the Frobenius–Perron dimension (= spectral radius) of the
golden mean adjacency matrix M = [[1,1],[1,0]] equals the golden ratio φ.
-/

namespace Omega.POM.CentralizerFPdim

open Omega.Graph

/-- The Frobenius–Perron dimension of the multiplicity matrix M = [[1,1],[1,0]] equals
    the golden ratio φ = (1+√5)/2. The proof assembles: (1) the characteristic polynomial
    is X²−X−1; (2) there exists a positive eigenvector with eigenvalue φ; (3) all real
    eigenvalues are bounded in modulus by φ.
    cor:pom-centralizer-fpdim-golden -/
theorem paper_centralizer_fpdim_golden :
    goldenMeanAdjacency.charpoly = Polynomial.X ^ 2 - Polynomial.X - 1 ∧
    (∃ v : Fin 2 → ℝ,
      (0 < v 0 ∧ 0 < v 1) ∧
      (goldenMeanAdjacencyℝ.mulVec v = fun i => Real.goldenRatio * v i) ∧
      (∀ μ : ℝ, (∃ w : Fin 2 → ℝ, w ≠ 0 ∧
        goldenMeanAdjacencyℝ.mulVec w = fun i => μ * w i) → |μ| ≤ Real.goldenRatio)) :=
  ⟨goldenMeanAdjacency_charpoly, goldenMeanAdjacency_pf_root_eq_goldenRatio⟩

end Omega.POM.CentralizerFPdim
