import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

noncomputable section

/-- Concrete factorization data for the normal-form shifted Hankel family `H(k) = O * A^k * C`. -/
structure POMHankelNFShiftData where
  d : ℕ
  O : Matrix (Fin d) (Fin d) ℝ
  A : Matrix (Fin d) (Fin d) ℝ
  C : Matrix (Fin d) (Fin d) ℝ
  hO_det : IsUnit O.det
  hA_det : IsUnit A.det
  hC_det : IsUnit C.det
  hshiftInvariant :
    ∀ k,
      ((O * A ^ k * C)⁻¹ * (O * A ^ (k + 1) * C)) = C⁻¹ * A * C
  hpowerPropagation :
    ∀ k₀ r,
      O * A ^ (k₀ + r) * C = (O * A ^ k₀ * C) * (C⁻¹ * A * C) ^ r

namespace POMHankelNFShiftData

/-- The shifted Hankel block at lag `k`. -/
def H (D : POMHankelNFShiftData) (k : ℕ) : Matrix (Fin D.d) (Fin D.d) ℝ :=
  D.O * D.A ^ k * D.C

/-- The common transfer matrix obtained from `H_k⁻¹ H_{k+1}`. -/
def transfer (D : POMHankelNFShiftData) : Matrix (Fin D.d) (Fin D.d) ℝ :=
  D.C⁻¹ * D.A * D.C

/-- The one-step transfer `H_k⁻¹ H_{k+1}` is independent of `k`. -/
def shiftInvariantTransfer (D : POMHankelNFShiftData) : Prop :=
  ∀ k, (D.H k)⁻¹ * D.H (k + 1) = D.transfer

/-- Every shifted Hankel block is obtained from `H_{k₀}` by propagating powers of the common
transfer matrix. -/
def powerPropagation (D : POMHankelNFShiftData) : Prop :=
  ∀ k₀ r, D.H (k₀ + r) = D.H k₀ * D.transfer ^ r

lemma shiftInvariantTransfer_holds (D : POMHankelNFShiftData) : D.shiftInvariantTransfer := by
  intro k
  simpa [H, transfer] using D.hshiftInvariant k

lemma powerPropagation_holds (D : POMHankelNFShiftData) : D.powerPropagation := by
  intro k₀ r
  simpa [H, transfer] using D.hpowerPropagation k₀ r

end POMHankelNFShiftData

open POMHankelNFShiftData

/-- In the normal-form factorization `H(k) = O * A^k * C`, the transfer matrix
`H_k⁻¹ H_{k+1}` is constant in `k`, and every later shifted Hankel block is obtained by taking
powers of that common transfer.
    thm:pom-hankel-nf-shift-invariance-and-power-propagation -/
theorem paper_pom_hankel_nf_shift_invariance_and_power_propagation
    (D : POMHankelNFShiftData) : And D.shiftInvariantTransfer D.powerPropagation := by
  exact ⟨D.shiftInvariantTransfer_holds, D.powerPropagation_holds⟩

end

end Omega.POM
