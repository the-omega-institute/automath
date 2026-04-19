import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic
import Omega.Zeta.FiniteDefectCompleteReconstruction
import Omega.Zeta.XiMarkovDerivativeDeterminantBadPrime

namespace Omega.Zeta

open Omega.CircleDimension

/-- The first Hankel block extracted from the finite jet `u_0, …, u_{2κ-1}`. -/
noncomputable def derivedHankelFiniteJetH0 {κ : ℕ} (D : FiniteDefectCompleteReconstructionData κ) :
    Matrix (Fin κ) (Fin κ) ℂ :=
  fun i j => atomicDefectSample D.deltaStep D.depths D.amplitudesXi (i.1 + j.1)

/-- The shifted Hankel block extracted from the same finite jet. -/
noncomputable def derivedHankelFiniteJetH1 {κ : ℕ} (D : FiniteDefectCompleteReconstructionData κ) :
    Matrix (Fin κ) (Fin κ) ℂ :=
  fun i j => atomicDefectSample D.deltaStep D.depths D.amplitudesXi (i.1 + j.1 + 1)

/-- The Gram-shift realization matrix `A = H₀⁻¹ H₁` attached to the finite jet. -/
noncomputable def derivedHankelFiniteJetShiftMatrix {κ : ℕ}
    (D : FiniteDefectCompleteReconstructionData κ) : Matrix (Fin κ) (Fin κ) ℂ :=
  (derivedHankelFiniteJetH0 D)⁻¹ * derivedHankelFiniteJetH1 D

/-- A prime is good for the arithmetic audit when it is prime and avoids the bad-prime set. -/
def derivedHankelGoodPrime
    (M : XiMarkovDerivativeDeterminantBadPrimeData) (p : ℕ) : Prop :=
  Nat.Prime p ∧ ¬ M.badPrime p

/-- Finite Hankel jets determine the reconstruction data, and any audited good prime keeps the
Green-kernel denominator nonzero modulo `p`. This packages the finite-sample Hankel blocks, the
shift matrix `A = H₀⁻¹ H₁`, the node/pole reconstruction interface, and the good-prime audit
certificate into one wrapper theorem. -/
theorem paper_derived_hankel_finite_jet_bad_prime_closure
    (κ : ℕ) (D : FiniteDefectCompleteReconstructionData κ)
    (M : XiMarkovDerivativeDeterminantBadPrimeData) (p : ℕ)
    (hp : derivedHankelGoodPrime M p) :
    D.kappaReadable ∧
      D.reconstructionFrom4KappaSamples ∧
      D.reconstructionFromMomentSegment ∧
      D.strictificationInvariant ∧
      (∀ i j, derivedHankelFiniteJetH0 D i j =
        atomicDefectSample D.deltaStep D.depths D.amplitudesXi (i.1 + j.1)) ∧
      (∀ i j, derivedHankelFiniteJetH1 D i j =
        atomicDefectSample D.deltaStep D.depths D.amplitudesXi (i.1 + j.1 + 1)) ∧
      derivedHankelFiniteJetShiftMatrix D =
        (derivedHankelFiniteJetH0 D)⁻¹ * derivedHankelFiniteJetH1 D ∧
      M.det_eq_charpoly_derivative ∧
      M.bad_prime_iff_double_root ∧
      M.green_denominator_obstruction ∧
      ((((M.greenDenominator : ℤ) : ZMod p) ≠ 0)) := by
  rcases hp with ⟨hpp, hpGood⟩
  rcases paper_xi_finite_defect_complete_reconstruction κ D with ⟨hkappa, h4k, h2k, hstrict⟩
  rcases paper_xi_markov_derivative_determinant_bad_prime M with ⟨hdet, hbad, hgreen⟩
  have hdenom : (((M.greenDenominator : ℤ) : ZMod p) ≠ 0) := by
    intro hzero
    exact hpGood ((hgreen.2 p hpp) hzero)
  refine ⟨hkappa, h4k, h2k, hstrict, ?_, ?_, rfl, hdet, hbad, hgreen, hdenom⟩
  · intro i j
    rfl
  · intro i j
    rfl

end Omega.Zeta
