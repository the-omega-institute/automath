import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.OperatorAlgebra

noncomputable section

/-- Finite fold fibers with explicit multiplicities `d(x)`. -/
structure FoldFiberMultiplicity where
  X : Type
  instDecEqX : DecidableEq X
  instFintypeX : Fintype X
  d : X → ℕ
  d_pos : ∀ x, 0 < d x

attribute [instance] FoldFiberMultiplicity.instDecEqX
attribute [instance] FoldFiberMultiplicity.instFintypeX

namespace FoldFiberMultiplicity

/-- The total finite microstate space above `X`. -/
abbrev TotalSpace (D : FoldFiberMultiplicity) :=
  Σ x : D.X, Fin (D.d x)

/-- Fiberwise averaging operator. -/
def conditionalExpectation (D : FoldFiberMultiplicity) (f : D.TotalSpace → ℝ) : D.X → ℝ :=
  fun x => (∑ i : Fin (D.d x), f ⟨x, i⟩) / (D.d x : ℝ)

/-- Counting-measure adjoint of the fiberwise average. -/
def conditionalExpectationAdjoint (D : FoldFiberMultiplicity) (g : D.X → ℝ) :
    D.TotalSpace → ℝ :=
  fun xi => g xi.1 / (D.d xi.1 : ℝ)

/-- The diagonal entries of `E_m E_m*`. -/
def diagonalEntry (D : FoldFiberMultiplicity) (x : D.X) : ℝ :=
  1 / (D.d x : ℝ)

/-- The singular value attached to the fiber over `x`. -/
def singularValue (D : FoldFiberMultiplicity) (x : D.X) : ℝ :=
  Real.sqrt (D.diagonalEntry x)

lemma diagonalEntry_nonneg (D : FoldFiberMultiplicity) (x : D.X) :
    0 ≤ D.diagonalEntry x := by
  unfold diagonalEntry
  positivity

lemma conditionalExpectation_comp_adjoint (D : FoldFiberMultiplicity) (g : D.X → ℝ)
    (x : D.X) :
    D.conditionalExpectation (D.conditionalExpectationAdjoint g) x = D.diagonalEntry x * g x := by
  have hd : (D.d x : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (D.d_pos x)
  unfold conditionalExpectation conditionalExpectationAdjoint diagonalEntry
  calc
    (∑ i : Fin (D.d x), g x / (D.d x : ℝ)) / (D.d x : ℝ)
        = ((D.d x : ℝ) * (g x / (D.d x : ℝ))) / (D.d x : ℝ) := by
            simp
    _ = (1 / (D.d x : ℝ)) * g x := by
          field_simp [hd]

lemma singularValue_sq (D : FoldFiberMultiplicity) (x : D.X) :
    D.singularValue x ^ 2 = D.diagonalEntry x := by
  unfold singularValue
  simpa [pow_two] using Real.sq_sqrt (D.diagonalEntry_nonneg x)

end FoldFiberMultiplicity

open FoldFiberMultiplicity

/-- For the finite fiber-average operator `E_m`, the composition `E_m E_m*` is diagonal with
entries `1 / d_m(x)`, so the singular values are exactly `d_m(x)^(-1/2)`.
    prop:fold-conditional-expectation-singular-spectrum -/
theorem paper_prop_fold_conditional_expectation_singular_spectrum (D : FoldFiberMultiplicity) :
    (∀ g x, D.conditionalExpectation (D.conditionalExpectationAdjoint g) x =
      D.diagonalEntry x * g x) ∧
      (∀ x, D.diagonalEntry x = 1 / (D.d x : ℝ)) ∧
      (∀ x, D.singularValue x ^ 2 = D.diagonalEntry x) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g x
    exact D.conditionalExpectation_comp_adjoint g x
  · intro x
    rfl
  · intro x
    exact D.singularValue_sq x

/-- Paper label: `prop:fold-condexp-singular-values`. The fiber-average compression has diagonal
`E E*` entries `1 / d(x)`, so the squared singular value over `x` is `1 / d(x)`. -/
theorem paper_fold_condexp_singular_values (D : FoldFiberMultiplicity) :
    (∀ g x, D.conditionalExpectation (D.conditionalExpectationAdjoint g) x =
      (1 / (D.d x : ℝ)) * g x) ∧
      (∀ x, D.singularValue x ^ 2 = 1 / (D.d x : ℝ)) := by
  refine ⟨?_, ?_⟩
  · intro g x
    simpa [FoldFiberMultiplicity.diagonalEntry] using D.conditionalExpectation_comp_adjoint g x
  · intro x
    simpa [FoldFiberMultiplicity.diagonalEntry] using D.singularValue_sq x

end

end Omega.OperatorAlgebra
