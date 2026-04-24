import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open BigOperators Matrix

/-- Concrete Gram-cluster data: `G = I + E`, the diagonal defect vanishes, off-diagonal entries are
uniformly exponentially small in the separation scale, and the log-determinant proxy `S` is
already decomposed into the quadratic trace term plus an explicit tail `R`. -/
structure paper_xi_hellinger_cluster_expansion_large_separation_Data where
  kappa : ℕ
  deltaMin : ℝ
  E : Matrix (Fin kappa) (Fin kappa) ℝ
  S : ℝ
  quadraticTraceTerm : ℝ
  R : ℝ
  hdiag : ∀ i, E i i = 0
  hbound : ∀ i j, i ≠ j →
    |E i j| ≤ (1 + deltaMin) * Real.exp (-deltaMin / 2)
  hcluster : S = quadraticTraceTerm + R
  htail :
    |R| ≤ (kappa : ℝ) ^ 3 * ((1 + deltaMin) * Real.exp (-deltaMin / 2)) ^ 3

/-- The Gram package `I + E`. -/
def xi_hellinger_cluster_expansion_large_separation_gram
    (D : paper_xi_hellinger_cluster_expansion_large_separation_Data) :
    Matrix (Fin D.kappa) (Fin D.kappa) ℝ :=
  1 + D.E

/-- Quadratic trace contribution in the cluster expansion. -/
def xi_hellinger_cluster_expansion_large_separation_mainTerm
    (D : paper_xi_hellinger_cluster_expansion_large_separation_Data) : ℝ :=
  D.quadraticTraceTerm

/-- Cubic tail scale coming from the uniform max-entry bound. -/
noncomputable def xi_hellinger_cluster_expansion_large_separation_tailBound
    (D : paper_xi_hellinger_cluster_expansion_large_separation_Data) : ℝ :=
  (D.kappa : ℝ) ^ 3 * ((1 + D.deltaMin) * Real.exp (-D.deltaMin / 2)) ^ 3

/-- Concrete statement of the large-separation cluster expansion package. -/
def paper_xi_hellinger_cluster_expansion_large_separation_statement
    (D : paper_xi_hellinger_cluster_expansion_large_separation_Data) : Prop :=
  xi_hellinger_cluster_expansion_large_separation_gram D = 1 + D.E ∧
    Matrix.trace D.E = 0 ∧
    (∀ i j, i ≠ j →
      |D.E i j| ≤ (1 + D.deltaMin) * Real.exp (-D.deltaMin / 2)) ∧
    D.S = xi_hellinger_cluster_expansion_large_separation_mainTerm D + D.R ∧
    |D.R| ≤ xi_hellinger_cluster_expansion_large_separation_tailBound D

lemma xi_hellinger_cluster_expansion_large_separation_trace_zero
    (D : paper_xi_hellinger_cluster_expansion_large_separation_Data) :
    Matrix.trace D.E = 0 := by
  simp [Matrix.trace, D.hdiag]

/-- Paper label: `prop:xi-hellinger-cluster-expansion-large-separation`. The concrete matrix
package `G = I + E` has vanishing linear trace term, uniformly exponentially small off-diagonal
entries, and the supplied quadratic-plus-tail decomposition of `S` yields the large-separation
cluster expansion together with its cubic remainder bound. -/
theorem paper_xi_hellinger_cluster_expansion_large_separation
    (D : paper_xi_hellinger_cluster_expansion_large_separation_Data) :
    paper_xi_hellinger_cluster_expansion_large_separation_statement D := by
  refine ⟨rfl, xi_hellinger_cluster_expansion_large_separation_trace_zero D, D.hbound, ?_, ?_⟩
  · simpa [xi_hellinger_cluster_expansion_large_separation_mainTerm] using D.hcluster
  · simpa [xi_hellinger_cluster_expansion_large_separation_tailBound] using D.htail

end Omega.Zeta
