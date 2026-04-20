import Mathlib.Tactic
import Omega.Folding.FoldMultiplicityEnergy

namespace Omega.Folding

/-- The collision probability attached to the fold multiplicity profile. -/
def foldMultiplicityCollisionProbability (m : ℕ) : ℚ :=
  foldMultiplicityEnergy m / (2 : ℚ) ^ (2 * m)

/-- The zero-mode share of the collision probability. -/
def foldMultiplicityZeroModeCollisionProbability (m : ℕ) : ℚ :=
  foldMultiplicityZeroMode m ^ 2 / (2 : ℚ) ^ (2 * m)

/-- The nonzero-mode share of the collision probability. -/
def foldMultiplicityNonzeroCollisionProbability (m : ℕ) : ℚ :=
  foldMultiplicityVariance m / (2 : ℚ) ^ (2 * m)

/-- Parseval collision package for the fold multiplicity profile: the normalized collision
probability splits into zero and nonzero Fourier contributions, and in this concrete model all of
the mass sits in the zero mode. -/
def FoldCollisionSpectrumIdentity (m : ℕ) : Prop :=
  foldMultiplicityCollisionProbability m =
      foldMultiplicityZeroModeCollisionProbability m +
        foldMultiplicityNonzeroCollisionProbability m ∧
    foldMultiplicityCollisionProbability m = 1 ∧
    foldMultiplicityZeroModeCollisionProbability m = 1 ∧
    foldMultiplicityNonzeroCollisionProbability m = 0

/-- Paper-facing collision-spectrum wrapper derived from the fold multiplicity Parseval identity.
    thm:fold-collision-spectrum -/
theorem paper_fold_collision_spectrum (m : Nat) : FoldCollisionSpectrumIdentity m := by
  rcases paper_fold_multiplicity_energy m with ⟨hEnergy, hVariance, hZero⟩
  have hDenom : (2 : ℚ) ^ (2 * m) ≠ 0 := by positivity
  have hZeroSq : foldMultiplicityZeroMode m ^ 2 = (2 : ℚ) ^ (2 * m) := by
    rw [hZero]
    calc
      ((2 : ℚ) ^ m) ^ 2 = (2 : ℚ) ^ (m * 2) := by rw [pow_mul]
      _ = (2 : ℚ) ^ (2 * m) := by simp [Nat.mul_comm]
  have hNonzero : foldMultiplicityVariance m = 0 := by
    rw [hVariance, foldMultiplicityNonzeroFourierEnergy, hZeroSq, sub_self]
  have hNonzeroFourier : foldMultiplicityNonzeroFourierEnergy m = 0 := by
    simpa [hVariance] using hNonzero
  unfold FoldCollisionSpectrumIdentity
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold foldMultiplicityCollisionProbability foldMultiplicityZeroModeCollisionProbability
      foldMultiplicityNonzeroCollisionProbability
    rw [hEnergy, hVariance]
    rw [foldMultiplicityFourierEnergy]
    ring_nf
  · unfold foldMultiplicityCollisionProbability
    rw [hEnergy, foldMultiplicityFourierEnergy, hNonzeroFourier, add_zero, hZeroSq]
    exact div_self hDenom
  · unfold foldMultiplicityZeroModeCollisionProbability
    rw [hZeroSq]
    exact div_self hDenom
  · unfold foldMultiplicityNonzeroCollisionProbability
    rw [hNonzero]
    simp

end Omega.Folding
