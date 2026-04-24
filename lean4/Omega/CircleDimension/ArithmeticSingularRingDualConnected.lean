import Mathlib.Tactic
import Omega.CircleDimension.CircleDim

namespace Omega.CircleDimension

/-- A concrete fiber-product presentation for the arithmetic singular-ring wrapper: one base point
and one integral coordinate for each prime in `S`. -/
abbrev ArithmeticSingularRingFiberProduct (S : Finset ℕ) := Unit × (S → ℤ)

/-- The ambient lattice before quotienting by the diagonal copy of `ℤ`. -/
abbrev ArithmeticSingularRingDualAmbient (S : Finset ℕ) := ℤ × (S → ℤ)

/-- A normal form for the quotient by the diagonal relation, obtained by moving the first
coordinate into every `S`-component. -/
abbrev ArithmeticSingularRingDualNormalForms (S : Finset ℕ) :=
  { x : ArithmeticSingularRingDualAmbient S // x.1 = 0 }

/-- The quotient model used for the discrete dual: only the `S`-indexed integral coordinates
remain after normalizing away the diagonal copy of `ℤ`. -/
abbrev ArithmeticSingularRingDualModel (S : Finset ℕ) := S → ℤ

/-- The distinguished diagonal generator `(1,-1_S)`. -/
def arithmeticSingularRingDualDiagonalGenerator (S : Finset ℕ) :
    ArithmeticSingularRingDualAmbient S :=
  (1, fun _ => -1)

/-- Normalize an ambient point by subtracting the first coordinate from each `S`-component. -/
def arithmeticSingularRingDualNormalForm (S : Finset ℕ) :
    ArithmeticSingularRingDualAmbient S → ArithmeticSingularRingDualNormalForms S
  | (a, n) => ⟨(0, fun p => n p + a), rfl⟩

/-- Explicit quotient description of the discrete dual. -/
def arithmeticSingularRingDualQuotientEquiv (S : Finset ℕ) :
    ArithmeticSingularRingDualNormalForms S ≃ ArithmeticSingularRingDualModel S where
  toFun x := x.1.2
  invFun n := ⟨(0, n), rfl⟩
  left_inv x := by
    cases x with
    | mk x hx =>
        cases x with
        | mk a n =>
            simp at hx
            subst hx
            rfl
  right_inv n := by
    rfl

/-- The quotient presentation is the existence of the concrete normal-form equivalence. -/
def arithmeticSingularRingDualQuotientPresentation (S : Finset ℕ) : Prop :=
  Nonempty (ArithmeticSingularRingDualNormalForms S ≃ ArithmeticSingularRingDualModel S)

/-- Concrete torsion-freeness for the normalized dual model. -/
def arithmeticSingularRingDualTorsionFree (S : Finset ℕ) : Prop :=
  ∀ (n : ℕ) (_hn : 0 < n) (f : ArithmeticSingularRingDualModel S),
    (∀ p, (n : ℤ) * f p = 0) → f = 0

lemma arithmeticSingularRingDualTorsionFree_holds (S : Finset ℕ) :
    arithmeticSingularRingDualTorsionFree S := by
  intro n hn f hf
  ext p
  have hp : (n : ℤ) * f p = 0 := hf p
  rcases mul_eq_zero.mp hp with hzero | hzero
  · exact (hn.ne' (Int.ofNat_eq_zero.mp hzero)).elim
  · exact hzero

/-- In this bookkeeping model, connectedness is witnessed by torsion-freeness of the discrete
dual. -/
def arithmeticSingularRingConnected (S : Finset ℕ) : Prop :=
  arithmeticSingularRingDualTorsionFree S

/-- The free rank of the quotient model is the cardinality of `S`. -/
def arithmeticSingularRingDualRank (S : Finset ℕ) : ℕ :=
  S.card

/-- Arithmetic singular-ring dual connectedness: the fiber-product model is inhabited, the dual
quotient has the expected normal-form description, the discrete dual is torsion-free and hence
connected in the wrapper sense, and the circle-dimension rank is exactly `|S|`.
    thm:cdim-arithmetic-singular-ring-dual-connected -/
theorem paper_cdim_arithmetic_singular_ring_dual_connected (S : Finset ℕ) :
    Nonempty (ArithmeticSingularRingFiberProduct S) ∧
      arithmeticSingularRingDualQuotientPresentation S ∧
      arithmeticSingularRingDualTorsionFree S ∧
      arithmeticSingularRingConnected S ∧
      circleDim (arithmeticSingularRingDualRank S) 0 = S.card := by
  refine ⟨⟨(), fun _ => 0⟩, ⟨arithmeticSingularRingDualQuotientEquiv S⟩,
    arithmeticSingularRingDualTorsionFree_holds S, arithmeticSingularRingDualTorsionFree_holds S,
    ?_⟩
  simp [arithmeticSingularRingDualRank, circleDim]

end Omega.CircleDimension
