import Omega.Multiscale.SolenoidFundamentalCurrentAndStokes

namespace Omega.Multiscale

noncomputable section

open NormalizedStokesFiniteCoverInverseTowerSystem

/-- Levelwise finite-correspondence data: `sourceDegree` and `targetDegree` are the covering
degrees of the two legs, and the equidegree hypothesis is encoded by `degree_eq`. -/
structure SolenoidFiniteCorrespondence where
  sourceDegree : ℕ → ℕ
  targetDegree : ℕ → ℕ
  sourceDegree_pos : ∀ n, 0 < sourceDegree n
  degree_eq : ∀ n, sourceDegree n = targetDegree n

namespace SolenoidFiniteCorrespondence

/-- Pull back along the target leg and normalize the pushforward along the source leg. -/
def levelTransfer (C : SolenoidFiniteCorrespondence) (ξ : ℕ → ℝ) (n : ℕ) : ℝ :=
  (C.sourceDegree n : ℝ)⁻¹ * (C.targetDegree n : ℝ) * ξ n

/-- The induced operator on cylindrical representatives is just the levelwise transfer sequence. -/
def cylindricalTransfer (C : SolenoidFiniteCorrespondence) (ξ : ℕ → ℝ) : ℕ → ℝ :=
  fun n => C.levelTransfer ξ n

lemma levelTransfer_eq_self (C : SolenoidFiniteCorrespondence) (ξ : ℕ → ℝ) (n : ℕ) :
    C.levelTransfer ξ n = ξ n := by
  have hdeg :
      (C.targetDegree n : ℝ) = (C.sourceDegree n : ℝ) := by
    exact_mod_cast (C.degree_eq n).symm
  have hsrc_ne :
      (C.sourceDegree n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (C.sourceDegree_pos n)
  unfold levelTransfer
  rw [hdeg]
  simp [hsrc_ne]

end SolenoidFiniteCorrespondence

open SolenoidFiniteCorrespondence

/-- The normalized bulk integral is preserved by the finite-correspondence transfer. -/
def solenoidTransferPreservesIntegral
    (S : NormalizedStokesFiniteCoverInverseTowerSystem) (C : SolenoidFiniteCorrespondence) : Prop :=
  ∀ n, C.cylindricalTransfer (fun k => solenoidFundamentalBulkCurrent S k) n =
    solenoidFundamentalBulkCurrent S n

/-- Exterior differentiation commutes with the cylindrical transfer. -/
def solenoidTransferCommutesWithDifferential
    (S : NormalizedStokesFiniteCoverInverseTowerSystem) (C : SolenoidFiniteCorrespondence) : Prop :=
  ∀ n, C.cylindricalTransfer (fun k => normalizedDifferential S k) n =
    C.cylindricalTransfer (fun k => solenoidFundamentalBoundaryCurrent S k) n

/-- Boundary restriction commutes with the cylindrical transfer. -/
def solenoidTransferCommutesWithBoundary
    (S : NormalizedStokesFiniteCoverInverseTowerSystem) (C : SolenoidFiniteCorrespondence) : Prop :=
  ∀ n, C.cylindricalTransfer (fun k => solenoidFundamentalBoundaryCurrent S k) n =
    solenoidFundamentalBoundaryCurrent S n

/-- An equidegree finite correspondence preserves the normalized cylindrical integral, and because
the transfer is the identity on normalized representatives it also commutes with the exterior
differential and boundary restriction, hence preserves the inverse-limit Stokes identity.
    prop:app-solenoid-stokes-equivariance-finite-correspondence -/
theorem paper_app_solenoid_stokes_equivariance_finite_correspondence
    (S : NormalizedStokesFiniteCoverInverseTowerSystem) (C : SolenoidFiniteCorrespondence) :
    solenoidTransferPreservesIntegral S C ∧
      solenoidTransferCommutesWithDifferential S C ∧
      solenoidTransferCommutesWithBoundary S C := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    simpa [SolenoidFiniteCorrespondence.cylindricalTransfer, solenoidFundamentalBulkCurrent] using
      C.levelTransfer_eq_self (fun k => normalizedBulk S k) n
  · intro n
    rw [SolenoidFiniteCorrespondence.cylindricalTransfer,
      SolenoidFiniteCorrespondence.cylindricalTransfer]
    rw [C.levelTransfer_eq_self (fun k => normalizedDifferential S k) n,
      C.levelTransfer_eq_self (fun k => solenoidFundamentalBoundaryCurrent S k) n]
    simpa [solenoidFundamentalBoundaryCurrent] using normalizedStokes_levelwise S n
  · intro n
    simpa [SolenoidFiniteCorrespondence.cylindricalTransfer, solenoidFundamentalBoundaryCurrent]
      using C.levelTransfer_eq_self (fun k => solenoidFundamentalBoundaryCurrent S k) n

end

end Omega.Multiscale
