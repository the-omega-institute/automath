import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete seed data for the singular-ring node-splitting package. -/
structure RealInput40SingularRingNodeSplittingData where
  dummy : Unit := ()

/-- The residual factor `Q(z,u)` from the audited real-input-40 spectral-collision certificate. -/
def realInput40CollisionQ (z u : ℝ) : ℝ :=
  1 - z - 6 * u * z ^ 2 + 2 * u * z ^ 3 + (9 * u ^ 2 - u) * z ^ 4 + (u - 3 * u ^ 2) * z ^ 5 -
    (u ^ 3 + 2 * u ^ 2) * z ^ 6 + (4 * u ^ 3 - 3 * u ^ 2) * z ^ 7 + (u ^ 3 - u ^ 4) * z ^ 8

/-- Local polynomial in the shifted coordinates `Z = z + 1`, `U = u - 1`. -/
def realInput40LocalNodePolynomial (Z U : ℝ) : ℝ :=
  realInput40CollisionQ (-1 + Z) (1 + U)

/-- Exact expansion of `Q(-1 + Z, 1 + U)` in the local coordinates. -/
def realInput40LocalNodeExpansion (Z U : ℝ) : ℝ :=
  -U ^ 4 * Z ^ 8 + 8 * U ^ 4 * Z ^ 7 - 28 * U ^ 4 * Z ^ 6 + 56 * U ^ 4 * Z ^ 5 -
    70 * U ^ 4 * Z ^ 4 + 56 * U ^ 4 * Z ^ 3 - 28 * U ^ 4 * Z ^ 2 + 8 * U ^ 4 * Z - U ^ 4 -
    3 * U ^ 3 * Z ^ 8 + 28 * U ^ 3 * Z ^ 7 - 113 * U ^ 3 * Z ^ 6 + 258 * U ^ 3 * Z ^ 5 -
    365 * U ^ 3 * Z ^ 4 + 328 * U ^ 3 * Z ^ 3 - 183 * U ^ 3 * Z ^ 2 + 58 * U ^ 3 * Z -
    8 * U ^ 3 - 3 * U ^ 2 * Z ^ 8 + 33 * U ^ 2 * Z ^ 7 - 152 * U ^ 2 * Z ^ 6 +
    384 * U ^ 2 * Z ^ 5 - 576 * U ^ 2 * Z ^ 4 + 517 * U ^ 2 * Z ^ 3 - 264 * U ^ 2 * Z ^ 2 +
    66 * U ^ 2 * Z - 5 * U ^ 2 - U * Z ^ 8 + 14 * U * Z ^ 7 - 77 * U * Z ^ 6 +
    219 * U * Z ^ 5 - 343 * U * Z ^ 4 + 290 * U * Z ^ 3 - 119 * U * Z ^ 2 + 17 * U * Z +
    Z ^ 7 - 10 * Z ^ 6 + 37 * Z ^ 5 - 62 * Z ^ 4 + 45 * Z ^ 3 - 10 * Z ^ 2

/-- Quadratic tangent cone at the singular ring node. -/
def realInput40NodeQuadraticCone (Z U : ℝ) : ℝ :=
  10 * Z ^ 2 - 17 * Z * U + 5 * U ^ 2

/-- The branch slopes are indexed by the signs `s = ±1`. -/
noncomputable def realInput40NodeSlope (s : ℝ) : ℝ :=
  (17 + s * Real.sqrt 89) / 20

/-- Quadratic branch coefficient determined by cancelling the cubic term. -/
noncomputable def realInput40NodeQuadraticCoeff (s : ℝ) : ℝ :=
  -(23 : ℝ) / 16 - s * 179 * Real.sqrt 89 / 1424

/-- Cubic branch coefficient determined by cancelling the quartic term. -/
noncomputable def realInput40NodeCubicCoeff (s : ℝ) : ℝ :=
  64969 / 20000 + s * 51245797 * Real.sqrt 89 / 158420000

/-- Linearized local branch through the singular node in the shifted coordinate `U = u - 1`. -/
noncomputable def realInput40NodeLinearBranch (s U : ℝ) : ℝ :=
  -1 + realInput40NodeSlope s * U

/-- Linearized eigenvalue branch `λ = 1 / z` attached to the local node branch. -/
noncomputable def realInput40NodeEigenvalueBranch (s U : ℝ) : ℝ :=
  1 / realInput40NodeLinearBranch s U

/-- Explicit ring branch on the unit circle. -/
noncomputable def realInput40ExplicitRingBranch (u : ℝ) : ℝ :=
  -Real.sqrt u

/-- Explicit eigenvalue branch corresponding to `z(u) = -√u`. -/
noncomputable def realInput40ExplicitRingEigenvalue (u : ℝ) : ℝ :=
  1 / realInput40ExplicitRingBranch u

/-- Coefficient of `U^2` after substituting `Z = α U + β U^2 + γ U^3`. -/
def realInput40NodeBranchCoeff2 (α : ℝ) : ℝ :=
  -10 * α ^ 2 + 17 * α - 5

/-- Coefficient of `U^3` after the same substitution. -/
def realInput40NodeBranchCoeff3 (α β : ℝ) : ℝ :=
  45 * α ^ 3 - 119 * α ^ 2 - 20 * α * β + 66 * α + 17 * β - 8

/-- Coefficient of `U^4` after the same substitution. -/
def realInput40NodeBranchCoeff4 (α β γ : ℝ) : ℝ :=
  -62 * α ^ 4 + 290 * α ^ 3 + 135 * α ^ 2 * β - 264 * α ^ 2 - 238 * α * β - 20 * α * γ +
    58 * α - 10 * β ^ 2 + 66 * β + 17 * γ - 1

lemma realInput40LocalNodePolynomial_eq_expansion (Z U : ℝ) :
    realInput40LocalNodePolynomial Z U = realInput40LocalNodeExpansion Z U := by
  unfold realInput40LocalNodePolynomial realInput40CollisionQ realInput40LocalNodeExpansion
  ring

lemma realInput40NodeBranchCoeffs_vanish (s : ℝ) (hs : s ^ 2 = 1) :
    realInput40NodeBranchCoeff2 (realInput40NodeSlope s) = 0 ∧
      realInput40NodeBranchCoeff3 (realInput40NodeSlope s) (realInput40NodeQuadraticCoeff s) = 0 ∧
      realInput40NodeBranchCoeff4
          (realInput40NodeSlope s)
          (realInput40NodeQuadraticCoeff s)
          (realInput40NodeCubicCoeff s) = 0 := by
  have hsqrt : Real.sqrt 89 ^ 2 = 89 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 89 by positivity)]
  have hsplit : s = 1 ∨ s = -1 := by
    have hmul : (s - 1) * (s + 1) = 0 := by
      nlinarith [hs]
    rcases eq_zero_or_eq_zero_of_mul_eq_zero hmul with hs1 | hs2
    · left
      linarith
    · right
      linarith
  rcases hsplit with rfl | rfl
  · constructor
    · unfold realInput40NodeBranchCoeff2 realInput40NodeSlope
      nlinarith
    constructor
    · unfold realInput40NodeBranchCoeff3 realInput40NodeSlope realInput40NodeQuadraticCoeff
      nlinarith
    · unfold realInput40NodeBranchCoeff4 realInput40NodeSlope realInput40NodeQuadraticCoeff
        realInput40NodeCubicCoeff
      nlinarith
  · constructor
    · unfold realInput40NodeBranchCoeff2 realInput40NodeSlope
      nlinarith
    constructor
    · unfold realInput40NodeBranchCoeff3 realInput40NodeSlope realInput40NodeQuadraticCoeff
      nlinarith
    · unfold realInput40NodeBranchCoeff4 realInput40NodeSlope realInput40NodeQuadraticCoeff
        realInput40NodeCubicCoeff
      nlinarith

namespace RealInput40SingularRingNodeSplittingData

/-- Concrete node-splitting statement: the local polynomial has the audited expansion, the tangent
cone has discriminant `89`, and the explicit `±` branch coefficients cancel the `U²`, `U³`, and
`U⁴` terms in the formal branch substitution. -/
def node_splitting_statement (_D : RealInput40SingularRingNodeSplittingData) : Prop :=
  (∀ Z U : ℝ, realInput40LocalNodePolynomial Z U = realInput40LocalNodeExpansion Z U) ∧
    (∀ s : ℝ, s ^ 2 = 1 →
      realInput40NodeBranchCoeff2 (realInput40NodeSlope s) = 0 ∧
        realInput40NodeBranchCoeff3
            (realInput40NodeSlope s)
            (realInput40NodeQuadraticCoeff s) = 0 ∧
          realInput40NodeBranchCoeff4
              (realInput40NodeSlope s)
              (realInput40NodeQuadraticCoeff s)
              (realInput40NodeCubicCoeff s) = 0) ∧
    realInput40NodeSlope 1 = (17 + Real.sqrt 89) / 20 ∧
    realInput40NodeSlope (-1) = (17 - Real.sqrt 89) / 20 ∧
    (17 : ℝ) ^ 2 - 4 * 10 * 5 = 89 ∧
    realInput40NodeSlope 1 ≠ realInput40NodeSlope (-1)

end RealInput40SingularRingNodeSplittingData

open RealInput40SingularRingNodeSplittingData

lemma realInput40NodeEigenvalueBranch_hasDerivAt (s : ℝ) :
    HasDerivAt (realInput40NodeEigenvalueBranch s) (-realInput40NodeSlope s) 0 := by
  have hLinear :
      HasDerivAt (fun U : ℝ => -1 + realInput40NodeSlope s * U) (realInput40NodeSlope s) 0 := by
    convert (hasDerivAt_const (x := 0) (-1)).add
      ((hasDerivAt_id 0).const_mul (realInput40NodeSlope s)) using 1
    ring
  have hValue : (-1 + realInput40NodeSlope s * (0 : ℝ)) ≠ 0 := by norm_num
  have hInv :
      HasDerivAt (fun U : ℝ => (-1 + realInput40NodeSlope s * U)⁻¹) (-realInput40NodeSlope s) 0 := by
    convert (hLinear.inv hValue) using 1
    ring
  unfold realInput40NodeEigenvalueBranch realInput40NodeLinearBranch
  simpa [one_div] using hInv

lemma realInput40ExplicitRingBranch_hasDerivAt :
    HasDerivAt realInput40ExplicitRingBranch (-(1 / 2)) 1 := by
  have hSqrt : HasDerivAt (fun u : ℝ => Real.sqrt u) (1 / (2 * Real.sqrt 1)) 1 :=
    Real.hasDerivAt_sqrt (by norm_num)
  simpa [realInput40ExplicitRingBranch] using hSqrt.neg

namespace RealInput40SingularRingNodeSplittingData

/-- First-order eigenvalue drifts at the singular ring node: the two linearized analytic branches
coming from the tangent cone have slopes `-(17 ± √89) / 20` in the shifted coordinate `U = u - 1`,
while the explicit unit-ring branch `z(u) = -√u` has first-order drift `-1/2` at `u = 1`. -/
def eigenvalueDriftStatement (_D : RealInput40SingularRingNodeSplittingData) : Prop :=
  HasDerivAt (realInput40NodeEigenvalueBranch 1) (-realInput40NodeSlope 1) 0 ∧
    HasDerivAt (realInput40NodeEigenvalueBranch (-1)) (-realInput40NodeSlope (-1)) 0 ∧
    HasDerivAt realInput40ExplicitRingBranch (-(1 / 2)) 1 ∧
    -realInput40NodeSlope 1 = -(17 + Real.sqrt 89) / 20 ∧
    -realInput40NodeSlope (-1) = -(17 - Real.sqrt 89) / 20

end RealInput40SingularRingNodeSplittingData

/-- Concrete singular-ring node-splitting package for the audited real-input-40 collision
polynomial.
    thm:real-input-40-singular-ring-node-splitting -/
theorem paper_real_input_40_singular_ring_node_splitting
    (D : RealInput40SingularRingNodeSplittingData) : D.node_splitting_statement := by
  refine ⟨realInput40LocalNodePolynomial_eq_expansion, realInput40NodeBranchCoeffs_vanish, ?_,
    ?_, by norm_num, ?_⟩
  · norm_num [realInput40NodeSlope]
  · unfold realInput40NodeSlope
    ring
  · have hsqrt : Real.sqrt 89 ≠ 0 := by positivity
    have hslope :
        Real.sqrt 89 ≠ -Real.sqrt 89 := by
      intro h
      have : Real.sqrt 89 = 0 := by
        nlinarith [h]
      exact hsqrt this
    intro h
    have h' : Real.sqrt 89 = -Real.sqrt 89 := by
      simpa [realInput40NodeSlope] using h
    exact hslope h'

/-- First-order eigenvalue drifts at the real-input-40 singular ring node.
    cor:real-input-40-singular-ring-eigenvalue-drift -/
theorem paper_real_input_40_singular_ring_eigenvalue_drift
    (D : RealInput40SingularRingNodeSplittingData) : D.eigenvalueDriftStatement := by
  refine ⟨realInput40NodeEigenvalueBranch_hasDerivAt 1,
    realInput40NodeEigenvalueBranch_hasDerivAt (-1), realInput40ExplicitRingBranch_hasDerivAt,
    ?_, ?_⟩
  · unfold realInput40NodeSlope
    ring
  · unfold realInput40NodeSlope
    ring

end Omega.Conclusion
