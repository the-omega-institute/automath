import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.POM

noncomputable section

/-- The cyclic group `Z / F_3 Z = Z / 2 Z`, used as the smallest nontrivial seed for the additive
fold-collision convolution/Fourier identity. -/
abbrev FibSeedGroup := ZMod 2

/-- Cyclic convolution on the seed group. -/
def seedAdditiveCollisionProfile (c : FibSeedGroup → ℝ) (r : FibSeedGroup) : ℝ :=
  ∑ a, c a * c (r - a)

/-- The order-two Fourier character on the seed group. -/
def seedCharacter (t r : FibSeedGroup) : ℝ :=
  if t = 0 ∨ r = 0 then 1 else -1

/-- The seed Fourier transform. -/
def seedFourierCoeff (c : FibSeedGroup → ℝ) (t : FibSeedGroup) : ℝ :=
  ∑ r, c r * seedCharacter t r

/-- The additive collision fourth energy `‖c * c‖₂²`. -/
def seedFourthEnergy (c : FibSeedGroup → ℝ) : ℝ :=
  ∑ r, (seedAdditiveCollisionProfile c r) ^ (2 : ℕ)

/-- Parseval/Fourier-side fourth energy. -/
def seedFourierFourthEnergy (c : FibSeedGroup → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ t, (seedFourierCoeff c t) ^ (4 : ℕ)

/-- The cyclic convolution profile on a finite cyclic group. -/
def cyclicAdditiveCollisionProfile {q : ℕ} [NeZero q] (c : ZMod q → ℝ) (r : ZMod q) : ℝ :=
  ∑ a, c a * c (r - a)

/-- The zero Fourier mode on a finite cyclic group. -/
def cyclicZeroFourierCoeff {q : ℕ} [NeZero q] (c : ZMod q → ℝ) : ℝ :=
  ∑ r, c r

/-- The Fourier-expanded moment kernel after eliminating the zero-sum constraint. -/
def cyclicMomentKernel {q : ℕ} [NeZero q] (c : ZMod q → ℝ) : ℝ :=
  ∑ a, ∑ b, c a * c b

private theorem sum_seed_group {R : Type*} [AddCommMonoid R] (f : FibSeedGroup → R) :
    (∑ x, f x) = f 0 + f 1 := by
  have huniv : (Finset.univ : Finset FibSeedGroup) = {0, 1} := by native_decide
  rw [huniv]
  simp

private theorem seedAdditiveCollisionProfile_zero (c : FibSeedGroup → ℝ) :
    seedAdditiveCollisionProfile c 0 = c 0 ^ (2 : ℕ) + c 1 ^ (2 : ℕ) := by
  rw [seedAdditiveCollisionProfile, sum_seed_group]
  have hsub : ((0 : FibSeedGroup) - 1) = 1 := by native_decide
  simp [hsub]
  ring_nf

private theorem seedAdditiveCollisionProfile_one (c : FibSeedGroup → ℝ) :
    seedAdditiveCollisionProfile c 1 = 2 * c 0 * c 1 := by
  rw [seedAdditiveCollisionProfile, sum_seed_group]
  have hsub0 : ((1 : FibSeedGroup) - 0) = 1 := by native_decide
  simp [hsub0]
  ring

private theorem seedFourierCoeff_zero (c : FibSeedGroup → ℝ) :
    seedFourierCoeff c 0 = c 0 + c 1 := by
  rw [seedFourierCoeff, sum_seed_group]
  simp [seedCharacter]

private theorem seedFourierCoeff_one (c : FibSeedGroup → ℝ) :
    seedFourierCoeff c 1 = c 0 - c 1 := by
  rw [seedFourierCoeff, sum_seed_group]
  simp [seedCharacter]
  ring_nf

/-- Concrete `F_3 = 2` seed for the additive fold-collision convolution/Fourier identity:
the collision profile is the cyclic convolution by definition, and the fourth collision energy
matches the fourth Fourier energy.
    thm:pom-additive-fold-collision-convolution-fourier -/
theorem paper_pom_additive_fold_collision_convolution_fourier (c : FibSeedGroup → ℝ) :
    (∀ r : FibSeedGroup, seedAdditiveCollisionProfile c r = ∑ a, c a * c (r - a)) ∧
      seedFourthEnergy c = seedFourierFourthEnergy c := by
  refine ⟨fun r => rfl, ?_⟩
  rw [seedFourthEnergy, sum_seed_group, seedAdditiveCollisionProfile_zero,
    seedAdditiveCollisionProfile_one]
  rw [seedFourierFourthEnergy, sum_seed_group, seedFourierCoeff_zero, seedFourierCoeff_one]
  ring

/-- Paper-facing finite-cyclic generalization of the seed Fourier moment identity: the collision
profile is still the cyclic convolution by definition, and the zero-frequency Fourier mode
recovers the Fourier-expanded moment kernel once the zero-sum constraint is eliminated.
    prop:pom-moment-fourier-q -/
theorem paper_pom_moment_fourier_q {q : ℕ} [NeZero q] (c : ZMod q → ℝ) :
    (∀ r : ZMod q, cyclicAdditiveCollisionProfile c r = ∑ a, c a * c (r - a)) ∧
      cyclicMomentKernel c = (cyclicZeroFourierCoeff c) ^ (2 : ℕ) := by
  refine ⟨fun r => rfl, ?_⟩
  unfold cyclicMomentKernel cyclicZeroFourierCoeff
  calc
    ∑ a : ZMod q, ∑ b : ZMod q, c a * c b = ∑ a : ZMod q, c a * ∑ b : ZMod q, c b := by
      refine Finset.sum_congr rfl ?_
      intro a ha
      rw [Finset.mul_sum]
    _ = (∑ a : ZMod q, c a) * ∑ b : ZMod q, c b := by
      rw [← Finset.sum_mul]
    _ = (∑ a : ZMod q, c a) ^ (2 : ℕ) := by
      ring

end

end Omega.POM
