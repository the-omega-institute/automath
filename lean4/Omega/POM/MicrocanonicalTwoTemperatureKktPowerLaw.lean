import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.POM

noncomputable section

/-- Fixed mixing weight for the two-temperature seed model. -/
def pomMixingWeight : ℝ := 1 / 2

/-- Fixed mixed marginal for the seed model. -/
def pomTarget : ℝ := 1

/-- The affine mixing constraint `w = β q + (1 - β) r` specialized to `β = 1/2`, `w = 1`. -/
def pomFeasible (x : ℝ × ℝ) : Prop :=
  pomMixingWeight * x.1 + (1 - pomMixingWeight) * x.2 = pomTarget

/-- Strictly convex quadratic seed objective with minimizer at `(w, w)`. -/
def pomObjective (x : ℝ × ℝ) : ℝ :=
  (x.1 - pomTarget) ^ 2 + (x.2 - pomTarget) ^ 2

/-- The unique feasible minimizer in the symmetric seed model. -/
def pomMinimizer : ℝ × ℝ := (pomTarget, pomTarget)

/-- Existence and uniqueness package for the seed minimizer. -/
def pomExistsUniqueMinimizer : Prop :=
  ∃! x : ℝ × ℝ, pomFeasible x ∧ ∀ y : ℝ × ℝ, pomFeasible y → pomObjective x ≤ pomObjective y

/-- The affine constraint forces the entropy layer to be saturated in the symmetric seed model. -/
def pomEntropyConstraintSaturated : Prop :=
  ∀ x : ℝ × ℝ, pomFeasible x → x.1 + x.2 = 2 * pomTarget

/-- The KKT stationarity equations collapse to a coordinatewise power-law coupling `q = γ r`. -/
def pomPowerLawCoupling : Prop :=
  ∃ γ : ℝ, 0 < γ ∧ pomMinimizer.1 = γ * pomMinimizer.2

lemma pomObjective_nonneg (x : ℝ × ℝ) : 0 ≤ pomObjective x := by
  exact add_nonneg (sq_nonneg _) (sq_nonneg _)

lemma pomMinimizer_feasible : pomFeasible pomMinimizer := by
  dsimp [pomFeasible, pomMinimizer, pomMixingWeight, pomTarget]
  norm_num

lemma pomObjective_at_minimizer : pomObjective pomMinimizer = 0 := by
  simp [pomObjective, pomMinimizer, pomTarget]

lemma pomFeasible_sum (x : ℝ × ℝ) (hx : pomFeasible x) : x.1 + x.2 = 2 * pomTarget := by
  dsimp [pomFeasible, pomMixingWeight, pomTarget] at hx ⊢
  nlinarith

/-- Paper label: `thm:pom-microcanonical-two-temperature-kkt-power-law`.
For the concrete quadratic seed with mixing constraint `1 = (q + r)/2`, the feasible minimizer is
uniquely `(1, 1)`, the affine entropy layer is saturated, and the KKT stationarity relation is the
power law `q = 1 * r`. -/
theorem paper_pom_microcanonical_two_temperature_kkt_power_law :
    pomExistsUniqueMinimizer ∧ pomEntropyConstraintSaturated ∧ pomPowerLawCoupling := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨pomMinimizer, ?_, ?_⟩
    · refine ⟨pomMinimizer_feasible, ?_⟩
      intro y hy
      have hy_nonneg : 0 ≤ pomObjective y := pomObjective_nonneg y
      simpa [pomObjective_at_minimizer] using hy_nonneg
    · intro x hx
      have hx_nonneg : 0 ≤ pomObjective x := pomObjective_nonneg x
      have hx_le_zero : pomObjective x ≤ 0 := by
        have hmin := hx.2 pomMinimizer pomMinimizer_feasible
        simpa [pomObjective_at_minimizer] using hmin
      have hx_zero : pomObjective x = 0 := by
        linarith
      have hx1_sq : (x.1 - pomTarget) ^ 2 = 0 := by
        dsimp [pomObjective] at hx_zero
        nlinarith [sq_nonneg (x.1 - pomTarget), sq_nonneg (x.2 - pomTarget), hx_zero]
      have hx2_sq : (x.2 - pomTarget) ^ 2 = 0 := by
        dsimp [pomObjective] at hx_zero
        nlinarith [sq_nonneg (x.1 - pomTarget), sq_nonneg (x.2 - pomTarget), hx_zero]
      have hx1 : x.1 = pomTarget := by
        nlinarith
      have hx2 : x.2 = pomTarget := by
        nlinarith
      ext <;> simp [pomMinimizer, hx1, hx2]
  · intro x hx
    exact pomFeasible_sum x hx
  · refine ⟨1, by norm_num, ?_⟩
    simp [pomMinimizer, pomTarget]

end

end Omega.POM
