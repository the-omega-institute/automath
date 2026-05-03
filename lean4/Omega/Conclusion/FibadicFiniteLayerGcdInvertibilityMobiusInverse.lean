import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Concrete finite block data for the finite-layer gcd inverse formula. -/
structure conclusion_fibadic_finite_layer_gcd_invertibility_mobius_inverse_data where
  Block : Type
  blockFintype : Fintype Block
  blockDecidableEq : DecidableEq Block
  active : Finset Block
  blockScalar : Block → ℚ
  lambda : ℕ → ℚ
  mobius : ℕ → ℚ
  multiplyIndex : ℕ → ℕ → ℕ
  mobiusSupport : ℕ → Finset ℕ

attribute [instance]
  conclusion_fibadic_finite_layer_gcd_invertibility_mobius_inverse_data.blockFintype
  conclusion_fibadic_finite_layer_gcd_invertibility_mobius_inverse_data.blockDecidableEq

/-- Scalar by which the finite-layer operator acts on a block; inactive blocks are normalized
to the identity scalar. -/
def conclusion_fibadic_finite_layer_gcd_invertibility_mobius_inverse_operatorScalar
    (D : conclusion_fibadic_finite_layer_gcd_invertibility_mobius_inverse_data)
    (d : D.Block) : ℚ :=
  if d ∈ D.active then D.blockScalar d else 1

/-- Pointwise two-sided invertibility of the block-diagonal scalar model. -/
def conclusion_fibadic_finite_layer_gcd_invertibility_mobius_inverse_pointwiseInvertible
    (D : conclusion_fibadic_finite_layer_gcd_invertibility_mobius_inverse_data) : Prop :=
  ∃ inverseScalar : D.Block → ℚ,
    ∀ d,
      conclusion_fibadic_finite_layer_gcd_invertibility_mobius_inverse_operatorScalar D d *
          inverseScalar d = 1 ∧
        inverseScalar d *
          conclusion_fibadic_finite_layer_gcd_invertibility_mobius_inverse_operatorScalar D d = 1

/-- Closed-form inverse scalar on each active block. -/
noncomputable def conclusion_fibadic_finite_layer_gcd_invertibility_mobius_inverse_blockInverse
    (D : conclusion_fibadic_finite_layer_gcd_invertibility_mobius_inverse_data)
    (_h : ∀ d ∈ D.active, D.blockScalar d ≠ 0) (d : D.Block) : ℚ :=
  if _ : d ∈ D.active then (D.blockScalar d)⁻¹ else 1

/-- The finite Möbius inverse coefficient attached to the chosen support ledger. -/
noncomputable def conclusion_fibadic_finite_layer_gcd_invertibility_mobius_inverse_beta
    (D : conclusion_fibadic_finite_layer_gcd_invertibility_mobius_inverse_data)
    (n : ℕ) : ℚ :=
  ∑ k ∈ D.mobiusSupport n, D.mobius k * D.lambda (D.multiplyIndex n k)

/-- The blockwise inverse and Möbius inversion formula for the finite layer. -/
def conclusion_fibadic_finite_layer_gcd_invertibility_mobius_inverse_data.inverseFormula
    (D : conclusion_fibadic_finite_layer_gcd_invertibility_mobius_inverse_data) : Prop :=
  (conclusion_fibadic_finite_layer_gcd_invertibility_mobius_inverse_pointwiseInvertible D ↔
    ∀ d ∈ D.active, D.blockScalar d ≠ 0) ∧
    (∀ h d,
      conclusion_fibadic_finite_layer_gcd_invertibility_mobius_inverse_operatorScalar D d *
            conclusion_fibadic_finite_layer_gcd_invertibility_mobius_inverse_blockInverse D h d =
          1 ∧
        conclusion_fibadic_finite_layer_gcd_invertibility_mobius_inverse_blockInverse D h d *
            conclusion_fibadic_finite_layer_gcd_invertibility_mobius_inverse_operatorScalar D d =
          1) ∧
      ∀ β : ℕ → ℚ,
        (∀ n,
            β n =
              ∑ k ∈ D.mobiusSupport n, D.mobius k * D.lambda (D.multiplyIndex n k)) ↔
          β = conclusion_fibadic_finite_layer_gcd_invertibility_mobius_inverse_beta D

/-- Paper label:
`thm:conclusion-fibadic-finite-layer-gcd-invertibility-mobius-inverse`. -/
theorem paper_conclusion_fibadic_finite_layer_gcd_invertibility_mobius_inverse
    (D : conclusion_fibadic_finite_layer_gcd_invertibility_mobius_inverse_data) :
    D.inverseFormula := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · rintro ⟨inverseScalar, hInverse⟩ d hd hzero
      have hleft := (hInverse d).1
      simp [conclusion_fibadic_finite_layer_gcd_invertibility_mobius_inverse_operatorScalar, hd,
        hzero] at hleft
    · intro hNonzero
      refine ⟨conclusion_fibadic_finite_layer_gcd_invertibility_mobius_inverse_blockInverse D
        hNonzero, ?_⟩
      intro d
      by_cases hd : d ∈ D.active
      · simp [conclusion_fibadic_finite_layer_gcd_invertibility_mobius_inverse_operatorScalar,
          conclusion_fibadic_finite_layer_gcd_invertibility_mobius_inverse_blockInverse, hd,
          hNonzero d hd]
      · simp [conclusion_fibadic_finite_layer_gcd_invertibility_mobius_inverse_operatorScalar,
          conclusion_fibadic_finite_layer_gcd_invertibility_mobius_inverse_blockInverse, hd]
  · intro h d
    by_cases hd : d ∈ D.active
    · simp [conclusion_fibadic_finite_layer_gcd_invertibility_mobius_inverse_operatorScalar,
        conclusion_fibadic_finite_layer_gcd_invertibility_mobius_inverse_blockInverse, hd, h d hd]
    · simp [conclusion_fibadic_finite_layer_gcd_invertibility_mobius_inverse_operatorScalar,
        conclusion_fibadic_finite_layer_gcd_invertibility_mobius_inverse_blockInverse, hd]
  · intro β
    constructor
    · intro hβ
      funext n
      simp [conclusion_fibadic_finite_layer_gcd_invertibility_mobius_inverse_beta, hβ n]
    · intro hβ n
      rw [hβ]
      rfl

end Omega.Conclusion
