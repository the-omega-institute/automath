import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Concrete finite character ledger for
`thm:conclusion-fibadic-newspace-orthogonal-decomposition`.

The character type is finite, every character has a recorded exact Fibonacci depth bounded by
`maxDepth`, and the two scalar projection ledgers record the old and new finite-layer projectors.
-/
structure conclusion_fibadic_newspace_orthogonal_decomposition_data where
  conclusion_fibadic_newspace_orthogonal_decomposition_Character : Type
  conclusion_fibadic_newspace_orthogonal_decomposition_fintype :
    Fintype conclusion_fibadic_newspace_orthogonal_decomposition_Character
  conclusion_fibadic_newspace_orthogonal_decomposition_decidableEq :
    DecidableEq conclusion_fibadic_newspace_orthogonal_decomposition_Character
  conclusion_fibadic_newspace_orthogonal_decomposition_depth :
    conclusion_fibadic_newspace_orthogonal_decomposition_Character → ℕ
  conclusion_fibadic_newspace_orthogonal_decomposition_maxDepth : ℕ
  conclusion_fibadic_newspace_orthogonal_decomposition_depth_le_max :
    ∀ χ,
      conclusion_fibadic_newspace_orthogonal_decomposition_depth χ ≤
        conclusion_fibadic_newspace_orthogonal_decomposition_maxDepth
  conclusion_fibadic_newspace_orthogonal_decomposition_oldProjectionScalar :
    ℕ → conclusion_fibadic_newspace_orthogonal_decomposition_Character → ℤ
  conclusion_fibadic_newspace_orthogonal_decomposition_newProjectionScalar :
    ℕ → conclusion_fibadic_newspace_orthogonal_decomposition_Character → ℤ
  conclusion_fibadic_newspace_orthogonal_decomposition_mobiusCoefficient : ℕ → ℕ → ℤ
  conclusion_fibadic_newspace_orthogonal_decomposition_mobiusProjectionScalar :
    ∀ d χ,
      conclusion_fibadic_newspace_orthogonal_decomposition_newProjectionScalar d χ =
        ∑ e ∈ (Finset.range (d + 1)).filter (fun e => e ∣ d),
          conclusion_fibadic_newspace_orthogonal_decomposition_mobiusCoefficient d e *
            conclusion_fibadic_newspace_orthogonal_decomposition_oldProjectionScalar e χ

attribute [instance]
  conclusion_fibadic_newspace_orthogonal_decomposition_data.conclusion_fibadic_newspace_orthogonal_decomposition_fintype
  conclusion_fibadic_newspace_orthogonal_decomposition_data.conclusion_fibadic_newspace_orthogonal_decomposition_decidableEq

namespace conclusion_fibadic_newspace_orthogonal_decomposition_data

/-- The finite set of characters of exact depth `d`. -/
def exactDepthLayer (D : conclusion_fibadic_newspace_orthogonal_decomposition_data)
    (d : ℕ) : Finset D.conclusion_fibadic_newspace_orthogonal_decomposition_Character :=
  Finset.univ.filter
    (fun χ => D.conclusion_fibadic_newspace_orthogonal_decomposition_depth χ = d)

/-- The finite dimension assigned to the exact-depth layer. -/
def finiteLayerDimension (D : conclusion_fibadic_newspace_orthogonal_decomposition_data)
    (d : ℕ) : ℕ :=
  (D.exactDepthLayer d).card

/-- Layer dimensions are obtained by counting the exact-depth character packet. -/
def layerDimension (D : conclusion_fibadic_newspace_orthogonal_decomposition_data) : Prop :=
  ∀ d,
    D.finiteLayerDimension d =
      (Finset.univ.filter
        (fun χ => D.conclusion_fibadic_newspace_orthogonal_decomposition_depth χ = d)).card

/-- The newspace dimension at depth `d` is the cardinality of the exact-depth layer. -/
def newspaceDimension (D : conclusion_fibadic_newspace_orthogonal_decomposition_data) : Prop :=
  ∀ d, D.finiteLayerDimension d = (D.exactDepthLayer d).card

/-- Each character belongs to exactly its own finite exact-depth packet. -/
def finiteLayerOrthogonalDirectSum
    (D : conclusion_fibadic_newspace_orthogonal_decomposition_data) : Prop :=
  ∀ χ, χ ∈ D.exactDepthLayer
    (D.conclusion_fibadic_newspace_orthogonal_decomposition_depth χ)

/-- The bounded exact-depth packets cover the whole finite character basis. -/
def globalOrthogonalDirectSum
    (D : conclusion_fibadic_newspace_orthogonal_decomposition_data) : Prop :=
  Finset.univ =
    (Finset.range
      (D.conclusion_fibadic_newspace_orthogonal_decomposition_maxDepth + 1)).biUnion
        (fun d => D.exactDepthLayer d)

/-- Finite divisor-lattice Möbius projection formula on every character. -/
def mobiusProjectionFormula
    (D : conclusion_fibadic_newspace_orthogonal_decomposition_data) : Prop :=
  ∀ d χ,
    D.conclusion_fibadic_newspace_orthogonal_decomposition_newProjectionScalar d χ =
      ∑ e ∈ (Finset.range (d + 1)).filter (fun e => e ∣ d),
        D.conclusion_fibadic_newspace_orthogonal_decomposition_mobiusCoefficient d e *
          D.conclusion_fibadic_newspace_orthogonal_decomposition_oldProjectionScalar e χ

end conclusion_fibadic_newspace_orthogonal_decomposition_data

open conclusion_fibadic_newspace_orthogonal_decomposition_data

/-- Paper label:
`thm:conclusion-fibadic-newspace-orthogonal-decomposition`. -/
theorem paper_conclusion_fibadic_newspace_orthogonal_decomposition
    (D : conclusion_fibadic_newspace_orthogonal_decomposition_data) :
    D.layerDimension ∧ D.newspaceDimension ∧ D.finiteLayerOrthogonalDirectSum ∧
      D.globalOrthogonalDirectSum ∧ D.mobiusProjectionFormula := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro d
    rfl
  · intro d
    rfl
  · intro χ
    simp [exactDepthLayer]
  · ext χ
    constructor
    · intro _hχ
      refine Finset.mem_biUnion.mpr ?_
      refine ⟨D.conclusion_fibadic_newspace_orthogonal_decomposition_depth χ, ?_, ?_⟩
      · exact Finset.mem_range.mpr
          (Nat.lt_succ_of_le
            (D.conclusion_fibadic_newspace_orthogonal_decomposition_depth_le_max χ))
      · simp [exactDepthLayer]
    · intro _hχ
      simp
  · exact D.conclusion_fibadic_newspace_orthogonal_decomposition_mobiusProjectionScalar

end Omega.Conclusion
