import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Complex.Basic

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- Concrete witness package for the finite cyclic-lift Artin factorization. The data records the
lift determinant, its character-twisted blocks, and the corresponding zeta factors. -/
structure FiniteRhPhaseLiftArtinData where
  q : ℕ
  liftDet : ℂ → ℂ
  twistedDet : Fin q → ℂ → ℂ
  liftZeta : ℂ → ℂ
  twistedZeta : Fin q → ℂ → ℂ
  liftZeta_eq_inv : ∀ z : ℂ, liftDet z ≠ 0 → liftZeta z = (liftDet z)⁻¹
  twistedZeta_eq_inv : ∀ k : Fin q, ∀ z : ℂ, twistedDet k z ≠ 0 → twistedZeta k z = (twistedDet k z)⁻¹
  determinantFactorization : ∀ z : ℂ, liftDet z = ∏ k : Fin q, twistedDet k z
  twisted_nonzero_of_lift_nonzero : ∀ z : ℂ, liftDet z ≠ 0 → ∀ k : Fin q, twistedDet k z ≠ 0

/-- Determinant form of the Artin factorization: the cyclic lift splits as the product of the
character blocks coming from the finite Fourier diagonalization of the permutation part. -/
def FiniteRhPhaseLiftArtinData.artinDeterminantFactorization
    (D : FiniteRhPhaseLiftArtinData) : Prop :=
  ∀ z : ℂ, D.liftDet z = ∏ k : Fin D.q, D.twistedDet k z

/-- Zeta form of the Artin factorization: after inverting the determinant blocks, the cyclic-lift
zeta factor becomes the product of the character-channel zeta factors. -/
def FiniteRhPhaseLiftArtinData.artinZetaFactorization
    (D : FiniteRhPhaseLiftArtinData) : Prop :=
  ∀ z : ℂ, D.liftDet z ≠ 0 → D.liftZeta z = ∏ k : Fin D.q, D.twistedZeta k z

/-- Paper-facing Artin factorization package for the finite RH phase lift. The determinant
factorization is recorded directly, and the zeta factorization follows by inverting the block
diagonal determinant identity. -/
theorem paper_finite_rh_phase_lift_artin (D : FiniteRhPhaseLiftArtinData) :
    D.artinDeterminantFactorization ∧ D.artinZetaFactorization := by
  refine ⟨D.determinantFactorization, ?_⟩
  intro z hz
  calc
    D.liftZeta z = (D.liftDet z)⁻¹ := D.liftZeta_eq_inv z hz
    _ = (∏ k : Fin D.q, D.twistedDet k z)⁻¹ := by rw [D.determinantFactorization z]
    _ = ∏ k : Fin D.q, (D.twistedDet k z)⁻¹ := by simp
    _ = ∏ k : Fin D.q, D.twistedZeta k z := by
      refine Finset.prod_congr rfl ?_
      intro k hk
      symm
      exact D.twistedZeta_eq_inv k z (D.twisted_nonzero_of_lift_nonzero z hz k)

end
end Omega.Zeta
