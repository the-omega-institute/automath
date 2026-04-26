import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Omega.POM.AdditiveFoldCollisionConvolutionFourier
import Omega.POM.Renyi2NearUniform
import Omega.POM.S2Plancherel

open Filter
open scoped BigOperators Topology

namespace Omega.POM

noncomputable section

/-- Paper label: `prop:pom-additive-fold-collision-bounds`. The seed additive-collision
convolution/Fourier identity, the `q = 2` moment congruence, and the `S₂` Plancherel package give
the two-sided `L²` bounds for a nonnegative count function on `Z / 2 Z`; the Fibonacci growth law
then transfers the collision input to the Rényi-`2` rate, and the rate bounds convert to the
corresponding entropy inequalities. -/
theorem paper_pom_additive_fold_collision_bounds
    (c : FibSeedGroup → ℝ) (hnonneg : ∀ r, 0 ≤ c r)
    (R S2 : ℕ → ℝ) (r2 r2add : ℝ)
    (hR : ∀ m, R m = ((Nat.fib (m + 2) : ℝ) * S2 m) / (4 : ℝ) ^ m)
    (hS2_pos : ∀ m, 0 < S2 m) (hr2 : 0 < r2) (hr2add : 0 < r2add)
    (hS2 :
      Tendsto (fun m : ℕ => Real.log (S2 m) / (m : ℝ)) atTop (nhds (Real.log r2)))
    (hRateLower : r2 ^ (2 : ℕ) ≤ r2add) (hRateUpper : r2add ≤ 4 * r2) :
    (∀ r : FibSeedGroup, seedAdditiveCollisionProfile c r = ∑ a, c a * c (r - a)) ∧
      seedFourthEnergy c = seedFourierFourthEnergy c ∧
      s2PlancherelFormula ∧
      cyclicMomentKernel (q := 2) c = (cyclicZeroFourierCoeff (q := 2) c) ^ (2 : ℕ) ∧
      (∑ r, (c r) ^ (2 : ℕ)) ^ (2 : ℕ) ≤ seedFourthEnergy c ∧
      seedFourthEnergy c ≤ (∑ r, c r) ^ (2 : ℕ) * ∑ r, (c r) ^ (2 : ℕ) ∧
      Tendsto (fun m : ℕ => Real.log (R m) / (m : ℝ)) atTop
        (nhds (Real.log (Real.goldenRatio * r2 / 4))) ∧
      Real.log (4 / r2) ≤ Real.log (16 / r2add) ∧
      Real.log (16 / r2add) ≤ 2 * Real.log (4 / r2) := by
  have hconv := paper_pom_additive_fold_collision_convolution_fourier c
  have hs2 : s2PlancherelFormula := paper_pom_s2_plancherel.1
  have hmoment :
      cyclicMomentKernel (q := 2) c = (cyclicZeroFourierCoeff (q := 2) c) ^ (2 : ℕ) :=
    (paper_pom_moment_fourier_q (q := 2) c).2
  have hgrowth := paper_pom_renyi2_near_uniform R S2 r2 hR hS2_pos hr2 hS2
  have huniv : (Finset.univ : Finset FibSeedGroup) = {0, 1} := by
    native_decide
  have hprofile0 :
      seedAdditiveCollisionProfile c 0 = c 0 ^ (2 : ℕ) + c 1 ^ (2 : ℕ) := by
    rw [seedAdditiveCollisionProfile, huniv]
    simp
    ring_nf
  have hprofile1 : seedAdditiveCollisionProfile c 1 = 2 * c 0 * c 1 := by
    rw [seedAdditiveCollisionProfile, huniv]
    have hsub0 : ((1 : FibSeedGroup) - 0) = 1 := by
      native_decide
    simp [hsub0]
    ring
  have henergy :
      seedFourthEnergy c =
        (c 0 ^ (2 : ℕ) + c 1 ^ (2 : ℕ)) ^ (2 : ℕ) + (2 * c 0 * c 1) ^ (2 : ℕ) := by
    rw [seedFourthEnergy, huniv]
    simp [hprofile0, hprofile1]
  have hnorm :
      (∑ r, (c r) ^ (2 : ℕ)) = c 0 ^ (2 : ℕ) + c 1 ^ (2 : ℕ) := by
    rw [huniv]
    simp
  have hmass : (∑ r, c r) = c 0 + c 1 := by
    rw [huniv]
    simp
  have hl2lower : (∑ r, (c r) ^ (2 : ℕ)) ^ (2 : ℕ) ≤ seedFourthEnergy c := by
    rw [hnorm, henergy]
    nlinarith [hnonneg 0, hnonneg 1]
  have hl2upper :
      seedFourthEnergy c ≤ (∑ r, c r) ^ (2 : ℕ) * ∑ r, (c r) ^ (2 : ℕ) := by
    have haux :
        (∑ r, c r) ^ (2 : ℕ) * ∑ r, (c r) ^ (2 : ℕ) - seedFourthEnergy c =
          2 * c 0 * c 1 * (c 0 - c 1) ^ (2 : ℕ) := by
      rw [henergy, hmass, hnorm]
      ring
    have haux_nonneg : 0 ≤ 2 * c 0 * c 1 * (c 0 - c 1) ^ (2 : ℕ) := by
      have hmul_nonneg : 0 ≤ 2 * c 0 * c 1 := by
        nlinarith [hnonneg 0, hnonneg 1]
      exact mul_nonneg hmul_nonneg (sq_nonneg (c 0 - c 1))
    nlinarith [haux_nonneg, haux]
  have hcollision_entropy_lower : Real.log (4 / r2) ≤ Real.log (16 / r2add) := by
    apply Real.log_le_log
    · positivity
    · have hr2_ne : r2 ≠ 0 := ne_of_gt hr2
      have hr2add_ne : r2add ≠ 0 := ne_of_gt hr2add
      field_simp [hr2_ne, hr2add_ne]
      nlinarith
  have hcollision_entropy_upper : Real.log (16 / r2add) ≤ 2 * Real.log (4 / r2) := by
    have hfrac : 16 / r2add ≤ (4 / r2) ^ (2 : ℕ) := by
      have hr2_ne : r2 ≠ 0 := ne_of_gt hr2
      have hr2add_ne : r2add ≠ 0 := ne_of_gt hr2add
      field_simp [hr2_ne, hr2add_ne]
      nlinarith
    have hlog :
        Real.log (16 / r2add) ≤ Real.log ((4 / r2) ^ (2 : ℕ)) := by
      apply Real.log_le_log
      · positivity
      · exact hfrac
    have hpow : Real.log ((4 / r2) ^ (2 : ℕ)) = 2 * Real.log (4 / r2) := by
      rw [show (4 / r2) ^ (2 : ℕ) = (4 / r2) * (4 / r2) by ring]
      rw [Real.log_mul (show 4 / r2 ≠ 0 by positivity) (show 4 / r2 ≠ 0 by positivity)]
      ring
    rw [hpow] at hlog
    exact hlog
  exact
    ⟨hconv.1, hconv.2, hs2, hmoment, hl2lower, hl2upper, hgrowth, hcollision_entropy_lower,
      hcollision_entropy_upper⟩

end

end Omega.POM
