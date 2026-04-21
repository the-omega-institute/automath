import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Basic
import Mathlib.Tactic
import Omega.Folding.Entropy

open Filter
open scoped Topology

namespace Omega.Folding

/-- Binary entropy term used in the escort Shannon-rate lock package. -/
noncomputable def fold_escort_groundstate_shannon_rate_lock_binary_entropy (t : ℝ) : ℝ :=
  -t * Real.log t - (1 - t) * Real.log (1 - t)

/-- Finite-data wrapper for the frozen escort Shannon-rate lock. The exact entropy decomposition
and the two asymptotic inputs are packaged explicitly so the normalized Shannon entropy can be
forced to the ground-state rate `gStar`. -/
structure fold_escort_groundstate_shannon_rate_lock_data where
  theta : ℕ → ℝ
  delta : ℕ → ℝ
  logGroundCard : ℕ → ℝ
  ambientLogCard : ℕ → ℝ
  tailEntropy : ℕ → ℝ
  shannonEntropy : ℕ → ℝ
  gStar : ℝ
  binaryEntropy_nonneg :
    ∀ m, 0 ≤ fold_escort_groundstate_shannon_rate_lock_binary_entropy (theta m)
  binaryEntropy_le :
    ∀ m, fold_escort_groundstate_shannon_rate_lock_binary_entropy (theta m) ≤ Real.log 2
  delta_nonneg : ∀ m, 0 ≤ delta m
  tailEntropy_nonneg : ∀ m, 0 ≤ tailEntropy m
  entropy_identity :
    ∀ m,
      shannonEntropy m =
        fold_escort_groundstate_shannon_rate_lock_binary_entropy (theta m) +
          theta m * logGroundCard m + delta m * tailEntropy m
  tailEntropy_le : ∀ m, tailEntropy m ≤ ambientLogCard m
  theta_tendsto : Tendsto theta atTop (𝓝 1)
  logGroundCard_rate :
    Tendsto (fun m => logGroundCard m / (m + 1 : ℝ)) atTop (𝓝 gStar)
  deltaAmbient_rate :
    Tendsto (fun m => delta m * ambientLogCard m / (m + 1 : ℝ)) atTop (𝓝 0)

/-- The escort Shannon entropy has the same normalized rate as the ground-state logarithmic growth.
-/
def fold_escort_groundstate_shannon_rate_lock_statement
    (D : fold_escort_groundstate_shannon_rate_lock_data) : Prop :=
  Tendsto (fun m => D.shannonEntropy m / (m + 1 : ℝ)) atTop (𝓝 D.gStar)

/-- Paper label: `thm:fold-escort-groundstate-shannon-rate-lock`. -/
theorem paper_fold_escort_groundstate_shannon_rate_lock
    (D : fold_escort_groundstate_shannon_rate_lock_data) :
    fold_escort_groundstate_shannon_rate_lock_statement D := by
  let fold_escort_groundstate_shannon_rate_lock_main : ℕ → ℝ :=
    fun m => D.theta m * (D.logGroundCard m / (m + 1 : ℝ))
  let fold_escort_groundstate_shannon_rate_lock_binary : ℕ → ℝ :=
    fun m =>
      fold_escort_groundstate_shannon_rate_lock_binary_entropy (D.theta m) / (m + 1 : ℝ)
  let fold_escort_groundstate_shannon_rate_lock_tail : ℕ → ℝ :=
    fun m => D.delta m * D.tailEntropy m / (m + 1 : ℝ)
  have hmain :
      Tendsto fold_escort_groundstate_shannon_rate_lock_main atTop (𝓝 D.gStar) := by
    simpa [fold_escort_groundstate_shannon_rate_lock_main, div_eq_mul_inv, mul_assoc,
      mul_left_comm, mul_comm] using D.theta_tendsto.mul D.logGroundCard_rate
  have hlog2_div :
      Tendsto (fun m : ℕ => Real.log 2 / (m + 1 : ℝ)) atTop (𝓝 0) := by
    have hdiv : Tendsto (fun m : ℕ => (1 : ℝ) / (m + 1 : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => Real.log 2) atTop (𝓝 (Real.log 2))).mul hdiv
  have hbinary :
      Tendsto fold_escort_groundstate_shannon_rate_lock_binary atTop (𝓝 0) := by
    refine Omega.Entropy.tendsto_zero_of_nonneg_le_of_tendsto_zero
      fold_escort_groundstate_shannon_rate_lock_binary
      (fun m => Real.log 2 / (m + 1 : ℝ))
      ?_ ?_ hlog2_div
    · intro m
      dsimp [fold_escort_groundstate_shannon_rate_lock_binary]
      exact div_nonneg (D.binaryEntropy_nonneg m) (by positivity)
    · intro m
      dsimp [fold_escort_groundstate_shannon_rate_lock_binary]
      exact div_le_div_of_nonneg_right (D.binaryEntropy_le m) (by positivity)
  have htail :
      Tendsto fold_escort_groundstate_shannon_rate_lock_tail atTop (𝓝 0) := by
    refine Omega.Entropy.tendsto_zero_of_nonneg_le_of_tendsto_zero
      fold_escort_groundstate_shannon_rate_lock_tail
      (fun m => D.delta m * D.ambientLogCard m / (m + 1 : ℝ))
      ?_ ?_ D.deltaAmbient_rate
    · intro m
      dsimp [fold_escort_groundstate_shannon_rate_lock_tail]
      exact div_nonneg (mul_nonneg (D.delta_nonneg m) (D.tailEntropy_nonneg m)) (by positivity)
    · intro m
      dsimp [fold_escort_groundstate_shannon_rate_lock_tail]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (D.tailEntropy_le m) (D.delta_nonneg m)) (by positivity)
  have herr :
      Tendsto
        (fun m =>
          fold_escort_groundstate_shannon_rate_lock_binary m +
            fold_escort_groundstate_shannon_rate_lock_tail m)
        atTop (𝓝 0) := by
    simpa using hbinary.add htail
  have hsum :
      Tendsto
        (fun m =>
          fold_escort_groundstate_shannon_rate_lock_main m +
            (fold_escort_groundstate_shannon_rate_lock_binary m +
              fold_escort_groundstate_shannon_rate_lock_tail m))
        atTop (𝓝 D.gStar) := by
    simpa [add_assoc] using hmain.add herr
  refine Filter.Tendsto.congr' (Filter.Eventually.of_forall fun m => ?_) hsum
  dsimp [fold_escort_groundstate_shannon_rate_lock_main,
    fold_escort_groundstate_shannon_rate_lock_binary,
    fold_escort_groundstate_shannon_rate_lock_tail]
  rw [D.entropy_identity m, add_div, add_div]
  ring

end Omega.Folding
