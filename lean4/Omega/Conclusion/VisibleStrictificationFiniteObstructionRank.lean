import Mathlib.Tactic

/-- Paper label: `thm:conclusion-visible-strictification-finite-obstruction-rank`. Three finite
obstruction indices that equal the same rank agree with each other, and the supplied
no-second-obstruction assertion is carried along. -/
theorem paper_conclusion_visible_strictification_finite_obstruction_rank
    (negativeSquares stableToeplitzInertia blaschkeDegree κ : ℕ)
    (hKernel : negativeSquares = κ) (hToeplitz : stableToeplitzInertia = κ)
    (hBlaschke : blaschkeDegree = κ) (noSecondFiniteObstruction : Prop)
    (hNoSecond : noSecondFiniteObstruction) :
    negativeSquares = stableToeplitzInertia ∧ stableToeplitzInertia = blaschkeDegree ∧
      negativeSquares = κ ∧ noSecondFiniteObstruction := by
  exact ⟨hKernel.trans hToeplitz.symm, hToeplitz.trans hBlaschke.symm, hKernel, hNoSecond⟩
