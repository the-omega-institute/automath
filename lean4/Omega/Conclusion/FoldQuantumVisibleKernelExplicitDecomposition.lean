import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Omega.Conclusion.ConclusionFoldQuantumVisibleBooleanization

namespace Omega.Conclusion

/-- Concrete multiplicity data for the visible kernel package: `n = |X_m|` visible atoms together
with their fiber multiplicities `d_x`. -/
structure conclusion_fold_quantum_visible_kernel_explicit_decomposition_data where
  n : ℕ
  conclusion_fold_quantum_visible_kernel_explicit_decomposition_fiberMultiplicity : Fin n → ℕ

/-- Off-diagonal matrix directions, encoded row by row using the missing-column parametrization
`Fin (n - 1)`. -/
abbrev conclusion_fold_quantum_visible_kernel_explicit_decomposition_offDiagonalDirection
    (n : ℕ) :=
  Σ _ : Fin n, Fin (n - 1)

/-- Heavy fibers are exactly those visible atoms with multiplicity at least `2`. -/
abbrev conclusion_fold_quantum_visible_kernel_explicit_decomposition_heavyFiber
    (D : conclusion_fold_quantum_visible_kernel_explicit_decomposition_data) :=
  {x : Fin D.n //
    2 ≤
      D.conclusion_fold_quantum_visible_kernel_explicit_decomposition_fiberMultiplicity x}

/-- The explicit kernel index set: all off-diagonal directions plus one extra generator for each
heavy fiber. -/
abbrev conclusion_fold_quantum_visible_kernel_explicit_decomposition_kernelDirection
    (D : conclusion_fold_quantum_visible_kernel_explicit_decomposition_data) :=
  conclusion_fold_quantum_visible_kernel_explicit_decomposition_offDiagonalDirection D.n ⊕
    conclusion_fold_quantum_visible_kernel_explicit_decomposition_heavyFiber D

/-- The heavy-fiber count `N_{≥ 2}(m)`. -/
def conclusion_fold_quantum_visible_kernel_explicit_decomposition_heavyCount
    (D : conclusion_fold_quantum_visible_kernel_explicit_decomposition_data) : ℕ :=
  Fintype.card
    (conclusion_fold_quantum_visible_kernel_explicit_decomposition_heavyFiber D)

/-- The visible kernel decomposition is encoded by the visible booleanization image statement
together with the explicit basis count `|X_m|(|X_m|-1) + N_{≥ 2}(m)`. -/
def conclusion_fold_quantum_visible_kernel_explicit_decomposition_data.has_explicit_kernel_decomposition
    (D : conclusion_fold_quantum_visible_kernel_explicit_decomposition_data) : Prop :=
  Set.range (@conclusion_fold_quantum_visible_booleanization_foldChannel D.n) =
      conclusion_fold_quantum_visible_booleanization_visibleAlgebra D.n ∧
    Nonempty
      (conclusion_fold_quantum_visible_kernel_explicit_decomposition_kernelDirection D ≃
        conclusion_fold_quantum_visible_kernel_explicit_decomposition_offDiagonalDirection D.n ⊕
          conclusion_fold_quantum_visible_kernel_explicit_decomposition_heavyFiber D) ∧
    Fintype.card
        (conclusion_fold_quantum_visible_kernel_explicit_decomposition_kernelDirection D) =
      D.n * (D.n - 1) +
        conclusion_fold_quantum_visible_kernel_explicit_decomposition_heavyCount D

lemma conclusion_fold_quantum_visible_kernel_explicit_decomposition_offDiagonal_card
    (n : ℕ) :
    Fintype.card
        (conclusion_fold_quantum_visible_kernel_explicit_decomposition_offDiagonalDirection n) =
      n * (n - 1) := by
  simp [conclusion_fold_quantum_visible_kernel_explicit_decomposition_offDiagonalDirection]

/-- Paper label: `thm:conclusion-fold-quantum-visible-kernel-explicit-decomposition`. -/
theorem paper_conclusion_fold_quantum_visible_kernel_explicit_decomposition
    (D : conclusion_fold_quantum_visible_kernel_explicit_decomposition_data) :
    D.has_explicit_kernel_decomposition := by
  refine ⟨(paper_conclusion_fold_quantum_visible_booleanization D.n).1, ?_, ?_⟩
  · exact ⟨Equiv.refl _⟩
  · simp [conclusion_fold_quantum_visible_kernel_explicit_decomposition_kernelDirection,
      conclusion_fold_quantum_visible_kernel_explicit_decomposition_heavyCount]

end Omega.Conclusion
