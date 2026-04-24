import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

open scoped BigOperators

noncomputable section

/-- Finite-dimensional proxy data for the weighted adjacency family
`M(u) = A₀ + u A₁`. The vectors `leftVec` and `rightVec` are normalized left/right Perron
eigenvectors for `A₀` with eigenvalue `lambda0`. -/
structure LambdaLinearResponseData where
  ι : Type
  instFintype : Fintype ι
  instDecidableEq : DecidableEq ι
  A0 : ι → ι → ℝ
  A1 : ι → ι → ℝ
  leftVec : ι → ℝ
  rightVec : ι → ℝ
  lambda0 : ℝ
  right_eigen : ∀ i, ∑ j : ι, A0 i j * rightVec j = lambda0 * rightVec i
  left_eigen : ∀ j, ∑ i : ι, leftVec i * A0 i j = lambda0 * leftVec j

attribute [instance] LambdaLinearResponseData.instFintype
attribute [instance] LambdaLinearResponseData.instDecidableEq

namespace LambdaLinearResponseData

/-- The affine weighted adjacency family `A₀ + u A₁`. -/
def affineAdjacency (D : LambdaLinearResponseData) (u : ℝ) : D.ι → D.ι → ℝ :=
  fun i j => D.A0 i j + u * D.A1 i j

/-- The normalization denominator `ℓᵀ r`. -/
def pairing (D : LambdaLinearResponseData) : ℝ :=
  ∑ i : D.ι, D.leftVec i * D.rightVec i

/-- The first-order numerator `ℓᵀ A₁ r`. -/
def firstOrderNumerator (D : LambdaLinearResponseData) : ℝ :=
  ∑ i : D.ι, D.leftVec i * ∑ j : D.ι, D.A1 i j * D.rightVec j

/-- The first-order response coefficient `c₁ = (ℓᵀ A₁ r) / (ℓᵀ r)`. -/
def firstOrderCoefficient (D : LambdaLinearResponseData) : ℝ :=
  D.firstOrderNumerator / D.pairing

/-- The left-right quotient of the affine family, viewed as the first-order Perron proxy. -/
def lambdaResponse (D : LambdaLinearResponseData) (u : ℝ) : ℝ :=
  (∑ i : D.ι, D.leftVec i * ∑ j : D.ι, D.affineAdjacency u i j * D.rightVec j) / D.pairing

lemma a0_right_pairing (D : LambdaLinearResponseData) :
    (∑ i : D.ι, D.leftVec i * ∑ j : D.ι, D.A0 i j * D.rightVec j) =
      D.lambda0 * D.pairing := by
  unfold pairing
  calc
    (∑ i : D.ι, D.leftVec i * ∑ j : D.ι, D.A0 i j * D.rightVec j)
        = ∑ i : D.ι, D.leftVec i * (D.lambda0 * D.rightVec i) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [D.right_eigen i]
    _ = ∑ i : D.ι, D.lambda0 * (D.leftVec i * D.rightVec i) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          ring
    _ = D.lambda0 * ∑ i : D.ι, D.leftVec i * D.rightVec i := by
          rw [Finset.mul_sum]

lemma a0_left_pairing (D : LambdaLinearResponseData) :
    (∑ j : D.ι, (∑ i : D.ι, D.leftVec i * D.A0 i j) * D.rightVec j) =
      D.lambda0 * D.pairing := by
  unfold pairing
  calc
    (∑ j : D.ι, (∑ i : D.ι, D.leftVec i * D.A0 i j) * D.rightVec j)
        = ∑ j : D.ι, (D.lambda0 * D.leftVec j) * D.rightVec j := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            rw [D.left_eigen j]
    _ = ∑ j : D.ι, D.lambda0 * (D.leftVec j * D.rightVec j) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          ring
    _ = D.lambda0 * ∑ j : D.ι, D.leftVec j * D.rightVec j := by
          rw [Finset.mul_sum]

end LambdaLinearResponseData

open LambdaLinearResponseData

/-- Paper label: `prop:lambda-linear-response`.
The left-right quotient of `A₀ + u A₁` has the linear expansion
`λ₀ + u (ℓᵀ A₁ r)/(ℓᵀ r)`, and the `A₀` contribution reduces to `λ₀ (ℓᵀ r)` from either the
right or left Perron eigenvector relation. -/
theorem paper_lambda_linear_response (D : LambdaLinearResponseData) (hpair : D.pairing ≠ 0) :
    (∀ u : ℝ,
      D.lambdaResponse u = D.lambda0 + u * D.firstOrderCoefficient) ∧
    (∑ i : D.ι, D.leftVec i * ∑ j : D.ι, D.A0 i j * D.rightVec j) =
        D.lambda0 * D.pairing ∧
      (∑ j : D.ι, (∑ i : D.ι, D.leftVec i * D.A0 i j) * D.rightVec j) =
        D.lambda0 * D.pairing := by
  refine ⟨?_, D.a0_right_pairing, D.a0_left_pairing⟩
  intro u
  unfold LambdaLinearResponseData.lambdaResponse
    LambdaLinearResponseData.firstOrderCoefficient
    LambdaLinearResponseData.firstOrderNumerator
    LambdaLinearResponseData.affineAdjacency
  let s0 : D.ι → ℝ := fun i => ∑ j : D.ι, D.A0 i j * D.rightVec j
  let s1 : D.ι → ℝ := fun i => ∑ j : D.ι, D.A1 i j * D.rightVec j
  have hsplit :
      (∑ i : D.ι, D.leftVec i * ∑ j : D.ι, (D.A0 i j + u * D.A1 i j) * D.rightVec j) =
        (∑ i : D.ι, D.leftVec i * s0 i) + u * ∑ i : D.ι, D.leftVec i * s1 i := by
    calc
      (∑ i : D.ι, D.leftVec i * ∑ j : D.ι, (D.A0 i j + u * D.A1 i j) * D.rightVec j)
          = ∑ i : D.ι, ((D.leftVec i * s0 i) + u * (D.leftVec i * s1 i)) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              calc
                D.leftVec i * ∑ j : D.ι, (D.A0 i j + u * D.A1 i j) * D.rightVec j
                    = D.leftVec i *
                        ((∑ j : D.ι, D.A0 i j * D.rightVec j) +
                          u * ∑ j : D.ι, D.A1 i j * D.rightVec j) := by
                            congr 1
                            calc
                              (∑ j : D.ι, (D.A0 i j + u * D.A1 i j) * D.rightVec j)
                                  = ∑ j : D.ι,
                                      (D.A0 i j * D.rightVec j + u * (D.A1 i j * D.rightVec j)) := by
                                        refine Finset.sum_congr rfl ?_
                                        intro j hj
                                        ring
                              _ = (∑ j : D.ι, D.A0 i j * D.rightVec j) +
                                    ∑ j : D.ι, u * (D.A1 i j * D.rightVec j) := by
                                      rw [Finset.sum_add_distrib]
                              _ = (∑ j : D.ι, D.A0 i j * D.rightVec j) +
                                    u * ∑ j : D.ι, D.A1 i j * D.rightVec j := by
                                      rw [Finset.mul_sum]
                _ = D.leftVec i * (s0 i + u * s1 i) := by
                      simp [s0, s1]
                _ = (D.leftVec i * s0 i) + u * (D.leftVec i * s1 i) := by
                      ring
      _ = (∑ i : D.ι, D.leftVec i * s0 i) + ∑ i : D.ι, u * (D.leftVec i * s1 i) := by
            rw [Finset.sum_add_distrib]
      _ = (∑ i : D.ι, D.leftVec i * s0 i) + u * ∑ i : D.ι, D.leftVec i * s1 i := by
            rw [Finset.mul_sum]
  calc
    (∑ i : D.ι, D.leftVec i * ∑ j : D.ι, (D.A0 i j + u * D.A1 i j) * D.rightVec j) / D.pairing
        = ((∑ i : D.ι, D.leftVec i * s0 i) + u * ∑ i : D.ι, D.leftVec i * s1 i) / D.pairing := by
            rw [hsplit]
    _ = (D.lambda0 * D.pairing + u * ∑ i : D.ι, D.leftVec i * s1 i) /
          D.pairing := by
            simp [s0, D.a0_right_pairing]
    _ = D.lambda0 + u * ((∑ i : D.ι, D.leftVec i * s1 i) / D.pairing) := by
          field_simp [hpair]
    _ = D.lambda0 + u * ((∑ i : D.ι, D.leftVec i * ∑ j : D.ι, D.A1 i j * D.rightVec j) / D.pairing) := by
          simp [s1]

end

end Omega.SyncKernelWeighted
