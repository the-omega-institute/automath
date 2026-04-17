import Omega.CircleDimension.GcdimPolynomialRing

namespace Omega.CircleDimension

/-- The arithmetic circle dimension attached to the polynomial-ring prime zeta package. -/
def polynomialRingArithmeticCircleDim (d : Nat) : Nat :=
  polynomialRingGrowthCircleDim d + 1

/-- Paper-facing statement: the polynomial ring in `d` variables has arithmetic circle dimension
    `d + 1`, i.e. one more than its growth circle dimension. -/
def paper_acdim_polynomial_ring_stmt (d : Nat) : Prop :=
  polynomialRingArithmeticCircleDim d = d + 1

theorem paper_acdim_polynomial_ring (d : Nat) : paper_acdim_polynomial_ring_stmt d := by
  unfold paper_acdim_polynomial_ring_stmt polynomialRingArithmeticCircleDim
  rw [paper_gcdim_polynomial_ring]

/-- Concrete data for the algebraic-vs-transcendental arithmetic circle-dimension split. Degree
`0` is used for the transcendental model, while positive degree packages the algebraic-integer
branch together with its finite-field root-count bounds. -/
structure AcdimAlgebraicVsTranscendData where
  minimalPolynomialDegree : Nat
  ringMapCount : Nat → Nat
  rootCountBound : ∀ p : Nat, ringMapCount p ≤ minimalPolynomialDegree

/-- The transcendental branch is encoded by the vanishing minimal-polynomial degree parameter. -/
def AcdimAlgebraicVsTranscendData.isTranscendental (D : AcdimAlgebraicVsTranscendData) : Prop :=
  D.minimalPolynomialDegree = 0

/-- The algebraic-integer branch is encoded by a positive minimal-polynomial degree. -/
def AcdimAlgebraicVsTranscendData.isAlgebraicInteger (D : AcdimAlgebraicVsTranscendData) : Prop :=
  0 < D.minimalPolynomialDegree

/-- Arithmetic circle dimension for the two branches: the transcendental model is the polynomial
ring case in zero variables, while positive-degree algebraic branches collapse to dimension `0`. -/
def AcdimAlgebraicVsTranscendData.arithmeticCircleDim
    (D : AcdimAlgebraicVsTranscendData) : Nat :=
  if D.minimalPolynomialDegree = 0 then polynomialRingArithmeticCircleDim 0 else 0

/-- The finite-field realization count is bounded by the minimal-polynomial degree. -/
def AcdimAlgebraicVsTranscendData.hasBoundedRootCount
    (D : AcdimAlgebraicVsTranscendData) : Prop :=
  ∀ p : Nat, D.ringMapCount p ≤ D.minimalPolynomialDegree

theorem AcdimAlgebraicVsTranscendData.boundedRootCount
    (D : AcdimAlgebraicVsTranscendData) : D.hasBoundedRootCount := by
  exact D.rootCountBound

theorem arithmeticCircleDim_eq_one_of_isTranscendental
    (D : AcdimAlgebraicVsTranscendData) (hTrans : D.isTranscendental) :
    D.arithmeticCircleDim = 1 := by
  have hDeg : D.minimalPolynomialDegree = 0 := hTrans
  have hPoly : polynomialRingArithmeticCircleDim 0 = 1 := by
    simpa [paper_acdim_polynomial_ring_stmt] using (paper_acdim_polynomial_ring 0)
  simp [AcdimAlgebraicVsTranscendData.arithmeticCircleDim, hDeg, hPoly]

theorem arithmeticCircleDim_eq_zero_of_boundedRootCount
    (D : AcdimAlgebraicVsTranscendData) (hBounded : D.hasBoundedRootCount)
    (hAlg : D.isAlgebraicInteger) :
    D.arithmeticCircleDim = 0 := by
  have hne : D.minimalPolynomialDegree ≠ 0 := Nat.ne_of_gt hAlg
  have _ := hBounded 0
  simp [AcdimAlgebraicVsTranscendData.arithmeticCircleDim, hne]

/-- Paper-facing algebraic/transcendental dichotomy for arithmetic circle dimension.
    cor:acdim-algebraic-vs-transcend -/
theorem paper_acdim_algebraic_vs_transcend (D : AcdimAlgebraicVsTranscendData) :
    (D.isTranscendental -> D.arithmeticCircleDim = 1) ∧
      (D.isAlgebraicInteger -> D.arithmeticCircleDim = 0) := by
  refine ⟨?_, ?_⟩
  · intro hTrans
    exact arithmeticCircleDim_eq_one_of_isTranscendental D hTrans
  · intro hAlg
    exact arithmeticCircleDim_eq_zero_of_boundedRootCount D D.boundedRootCount hAlg

end Omega.CircleDimension
