import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace Omega.GU

open scoped BigOperators

/-- The diagonal semiaxis attached to the `i`-th prime-power weight `pᵢ ^ rᵢ` is
`pᵢ ^ (rᵢ / 2)`. -/
noncomputable def godelAxisScale {n : ℕ} (p r : Fin n → ℕ) (i : Fin n) : ℝ :=
  (p i : ℝ) ^ ((r i : ℝ) / 2)

/-- Determinant/volume scaling for the diagonal transport map. -/
noncomputable def godelEllipsoidVolumeScale {n : ℕ} (p r : Fin n → ℕ) : ℝ :=
  ∏ i, godelAxisScale p r i

/-- The Gödel prime-power norm `N(r) = ∏ pᵢ ^ rᵢ`. -/
noncomputable def godelPrimePowerNorm {n : ℕ} (p r : Fin n → ℕ) : ℝ :=
  ∏ i, (p i : ℝ) ^ (r i : ℝ)

/-- The diagonal ellipsoid transport scales volume by `∏ pᵢ^(rᵢ/2)`, so the squared scaling factor
is exactly `N(r)`. Taking logarithms recovers the additive prime-power identity.
    thm:group-jg-godel-ellipsoid-volume -/
theorem paper_group_jg_godel_ellipsoid_volume
    {n : ℕ} (p r : Fin n → ℕ) (hp : ∀ i, 2 ≤ p i) :
    godelEllipsoidVolumeScale p r ^ 2 = godelPrimePowerNorm p r ∧
      Real.log (godelPrimePowerNorm p r) = ∑ i, (r i : ℝ) * Real.log (p i : ℝ) := by
  have hp_pos : ∀ i, 0 < (p i : ℝ) := fun i => by exact_mod_cast lt_of_lt_of_le zero_lt_two (hp i)
  have hp_nonneg : ∀ i, 0 ≤ (p i : ℝ) := fun i => (hp_pos i).le
  have hp_ne : ∀ i, (p i : ℝ) ≠ 0 := fun i => ne_of_gt (hp_pos i)
  refine ⟨?_, ?_⟩
  · unfold godelEllipsoidVolumeScale godelPrimePowerNorm godelAxisScale
    calc
      (∏ i, (p i : ℝ) ^ ((r i : ℝ) / 2)) ^ 2
          = ∏ i, ((p i : ℝ) ^ ((r i : ℝ) / 2)) ^ 2 := by
              simp [pow_two, Finset.prod_mul_distrib]
      _ = ∏ i, (p i : ℝ) ^ (((r i : ℝ) / 2) * 2) := by
            refine Finset.prod_congr rfl ?_
            intro i hi
            rw [← Real.rpow_natCast, show (2 : ℝ) = (2 : ℕ) by norm_num,
              ← Real.rpow_mul (hp_nonneg i)]
      _ = ∏ i, (p i : ℝ) ^ (r i : ℝ) := by
            refine Finset.prod_congr rfl ?_
            intro i hi
            congr 1
            ring
  · unfold godelPrimePowerNorm
    rw [Real.log_prod]
    · refine Finset.sum_congr rfl ?_
      intro i hi
      rw [Real.log_rpow (hp_pos i)]
    · intro i hi
      exact ne_of_gt (Real.rpow_pos_of_pos (hp_pos i) _)

end Omega.GU
