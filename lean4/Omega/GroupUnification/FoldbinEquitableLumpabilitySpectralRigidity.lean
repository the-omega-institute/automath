import Mathlib.Data.Rat.Defs
import Mathlib.Data.Set.Basic
import Mathlib.Tactic

namespace Omega.GroupUnification

/-- Concrete data for an equitable quotient of a hypercube adjacency operator. The quotient
eigenvalues are the ones that admit a lift through the intertwining matrix, and the random-walk
spectrum is obtained by scaling adjacency eigenvalues by the reciprocal block size. -/
structure EquitableHypercubeQuotientData where
  quotientBlockCount : ℕ
  hypercubeAdjacencySpectrum : Set ℚ
  quotientEigenvalueCandidates : Set ℚ

/-- Quotient eigenvalues are exactly those candidate values that also lift to hypercube adjacency
eigenvalues. -/
def EquitableHypercubeQuotientData.quotientSpectrum
    (D : EquitableHypercubeQuotientData) : Set ℚ :=
  {x | x ∈ D.quotientEigenvalueCandidates ∧ x ∈ D.hypercubeAdjacencySpectrum}

/-- The quotient random-walk spectrum is obtained from the quotient adjacency spectrum by dividing
by the block count plus one. -/
def EquitableHypercubeQuotientData.markovSpectrum
    (D : EquitableHypercubeQuotientData) : Set ℚ :=
  {x | ∃ y ∈ D.quotientSpectrum, x = y / (D.quotientBlockCount + 1 : ℚ)}

/-- The ambient hypercube walk spectrum is obtained from the adjacency spectrum using the same
normalization factor. -/
def EquitableHypercubeQuotientData.hypercubeWalkSpectrum
    (D : EquitableHypercubeQuotientData) : Set ℚ :=
  {x | ∃ y ∈ D.hypercubeAdjacencySpectrum, x = y / (D.quotientBlockCount + 1 : ℚ)}

/-- Paper-facing spectral rigidity package for foldbin equitable lumpability: any lifted quotient
eigenvalue is already an adjacency eigenvalue of the hypercube, and dividing by the common block
count keeps the quotient walk spectrum inside the ambient walk spectrum.
    thm:foldbin-equitable-lumpability-spectral-rigidity -/
theorem paper_foldbin_equitable_lumpability_spectral_rigidity
    (D : EquitableHypercubeQuotientData) :
    D.quotientSpectrum ⊆ D.hypercubeAdjacencySpectrum ∧
      D.markovSpectrum ⊆ D.hypercubeWalkSpectrum := by
  refine ⟨?_, ?_⟩
  · intro x hx
    exact hx.2
  · intro x hx
    rcases hx with ⟨y, hy, rfl⟩
    exact ⟨y, hy.2, rfl⟩

end Omega.GroupUnification
