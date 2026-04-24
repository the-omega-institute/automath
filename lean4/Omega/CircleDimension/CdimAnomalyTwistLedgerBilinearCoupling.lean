import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

namespace Omega.CircleDimension

open scoped BigOperators

/-- The free `ℤ^s` coordinates used to model the torsion-valued twist parameter in a finite chart.
-/
abbrev TwistTorsionVector (s : ℕ) := Fin s → ℤ

/-- The tensor character `d : ℤ^r ⊗ F → ℤ` written in coordinates. -/
abbrev TwistTensorComponent (r s : ℕ) := Fin r → Fin s → ℤ

/-- The wedge character `θ : ∧² ℤ^r → ℤ` written in coordinates. -/
abbrev TwistWedgeComponent (r : ℕ) := Fin r → Fin r → ℤ

/-- The `∧² F` summand of the discrete anomaly ledger. -/
abbrev TwistTorsionComponent (s : ℕ) := Fin s → Fin s → ℤ

/-- Coordinate package for the anomaly ledger decomposition
`∧² ℤ^r ⊕ (ℤ^r ⊗ F) ⊕ ∧² F`. -/
structure CdimAnomalyTwistLedgerState (r s : ℕ) where
  wedge : TwistWedgeComponent r
  tensor : TwistTensorComponent r s
  torsion : TwistTorsionComponent s

/-- Evaluation of the tensor component `d` against a torsion coordinate vector. -/
def tensorCoordinateEval {r s : ℕ} (d : TwistTensorComponent r s)
    (x : Fin r) (f : TwistTorsionVector s) : ℤ :=
  ∑ a : Fin s, d x a * f a

/-- The bilinear correction term obtained by antisymmetrizing the tensor contribution. -/
def twistLedgerBilinearCoupling {r s : ℕ} (lam : Fin r → TwistTorsionVector s)
    (d : TwistTensorComponent r s) : TwistWedgeComponent r :=
  fun x y => tensorCoordinateEval d x (lam y) - tensorCoordinateEval d y (lam x)

/-- Pullback of the anomaly ledger along the twist automorphism `ψ_λ(x,f) = (x, f + λ(x))`. -/
def twistLedgerPullback {r s : ℕ} (lam : Fin r → TwistTorsionVector s)
    (L : CdimAnomalyTwistLedgerState r s) : CdimAnomalyTwistLedgerState r s where
  wedge := L.wedge + twistLedgerBilinearCoupling lam L.tensor
  tensor := L.tensor
  torsion := L.torsion

/-- Paper label: `thm:cdim-anomaly-twist-ledger-bilinear-coupling`.
In coordinates, the twist pullback modifies only the `∧² ℤ^r` summand by the antisymmetrized
tensor correction, and the correction is bilinear in the twist parameter and the tensor ledger. -/
theorem paper_cdim_anomaly_twist_ledger_bilinear_coupling
    {r s : ℕ} (lam lam' : Fin r → TwistTorsionVector s) (d d' : TwistTensorComponent r s)
    (L : CdimAnomalyTwistLedgerState r s) :
    twistLedgerPullback lam L =
      { wedge := L.wedge + twistLedgerBilinearCoupling lam L.tensor
        tensor := L.tensor
        torsion := L.torsion } ∧
      (∀ x y,
        twistLedgerBilinearCoupling lam L.tensor x y =
          tensorCoordinateEval L.tensor x (lam y) - tensorCoordinateEval L.tensor y (lam x)) ∧
      twistLedgerBilinearCoupling (lam + lam') d =
        twistLedgerBilinearCoupling lam d + twistLedgerBilinearCoupling lam' d ∧
      twistLedgerBilinearCoupling lam (d + d') =
        twistLedgerBilinearCoupling lam d + twistLedgerBilinearCoupling lam d' ∧
      ∀ x y,
        twistLedgerBilinearCoupling lam d y x = -twistLedgerBilinearCoupling lam d x y := by
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · intro x y
    rfl
  · funext x y
    unfold twistLedgerBilinearCoupling tensorCoordinateEval
    simp only [Pi.add_apply]
    rw [show ∑ a : Fin s, d x a * (lam y a + lam' y a) =
        ∑ a : Fin s, d x a * lam y a + ∑ a : Fin s, d x a * lam' y a by
          simp [mul_add, Finset.sum_add_distrib]]
    rw [show ∑ a : Fin s, d y a * (lam x a + lam' x a) =
        ∑ a : Fin s, d y a * lam x a + ∑ a : Fin s, d y a * lam' x a by
          simp [mul_add, Finset.sum_add_distrib]]
    abel
  · funext x y
    unfold twistLedgerBilinearCoupling tensorCoordinateEval
    simp only [Pi.add_apply]
    rw [show ∑ a : Fin s, (d x a + d' x a) * lam y a =
        ∑ a : Fin s, d x a * lam y a + ∑ a : Fin s, d' x a * lam y a by
          simp [add_mul, Finset.sum_add_distrib]]
    rw [show ∑ a : Fin s, (d y a + d' y a) * lam x a =
        ∑ a : Fin s, d y a * lam x a + ∑ a : Fin s, d' y a * lam x a by
          simp [add_mul, Finset.sum_add_distrib]]
    abel
  · intro x y
    unfold twistLedgerBilinearCoupling
    ring

end Omega.CircleDimension
