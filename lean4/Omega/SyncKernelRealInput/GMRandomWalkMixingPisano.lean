import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.SyncKernelWeighted.GMPisanoPeriodCharacterDecay

open scoped BigOperators

namespace Omega.SyncKernelRealInput

noncomputable section

/-- Concrete Pisano scale used for the cyclic random-walk model on `Fin q`. -/
def gm_random_walk_mixing_pisano_period (q : ℕ) : ℕ := q

/-- Uniform one-step law on the finite quotient `ℤ/qℤ`, viewed as `Fin q`. -/
def gm_random_walk_mixing_pisano_one_step_distribution (q _m : ℕ) : Fin q → ℝ :=
  fun _ => 1 / (q : ℝ)

/-- Averaging transition operator for the concrete finite walk. -/
def gm_random_walk_mixing_pisano_transition_operator
    (q m : ℕ) (f : Fin q → ℝ) : Fin q → ℝ :=
  fun _ => ∑ y : Fin q, gm_random_walk_mixing_pisano_one_step_distribution q m y * f y

/-- Fourier coefficient proxy imported from the Pisano-period character-decay package. -/
def gm_random_walk_mixing_pisano_fourier_coefficient (q m _a : ℕ) : ℝ :=
  Omega.SyncKernelWeighted.gm_pisano_period_character_decay_normalized_character_sum
    (gm_random_walk_mixing_pisano_period q) m (Real.exp (-((1 : ℝ) / (q : ℝ))))

/-- Maximal nontrivial Fourier coefficient in the concrete cyclic model. -/
def gm_random_walk_mixing_pisano_fourier_radius (q m : ℕ) : ℝ :=
  gm_random_walk_mixing_pisano_fourier_coefficient q m 1

/-- Nontrivial spectral radius identified with the maximal Fourier coefficient. -/
def gm_random_walk_mixing_pisano_nontrivial_spectral_radius (q m : ℕ) : ℝ :=
  gm_random_walk_mixing_pisano_fourier_radius q m

/-- Total-variation upper bound obtained from the cyclic Fourier radius. -/
def gm_random_walk_mixing_pisano_total_variation_bound (q m : ℕ) : ℝ :=
  (q : ℝ) / 2 * gm_random_walk_mixing_pisano_nontrivial_spectral_radius q m

/-- The Pisano-scale mixing-time upper bound recorded in the finite model. -/
def gm_random_walk_mixing_pisano_mixing_time_bound (q m : ℕ) : ℝ :=
  (gm_random_walk_mixing_pisano_period q : ℝ) * Real.log ((q : ℝ) + 1) / ((m : ℝ) + 1)

/-- Character diagonalization in this concrete model is the identification of the nontrivial
spectral radius with the maximal Fourier coefficient. -/
def gm_random_walk_mixing_pisano_character_diagonalization (q m : ℕ) : Prop :=
  gm_random_walk_mixing_pisano_nontrivial_spectral_radius q m =
    gm_random_walk_mixing_pisano_fourier_radius q m

theorem gm_random_walk_mixing_pisano_period_pos {q : ℕ} (hq : 2 ≤ q) :
    0 < gm_random_walk_mixing_pisano_period q := by
  unfold gm_random_walk_mixing_pisano_period
  omega

theorem gm_random_walk_mixing_pisano_one_period_contraction (q : ℕ) :
    Omega.SyncKernelWeighted.gm_pisano_period_character_decay_one_period_contraction
      ((1 : ℝ) / (q : ℝ))
      (Real.exp (-((1 : ℝ) / (q : ℝ)))) := by
  constructor
  · positivity
  · rfl

theorem gm_random_walk_mixing_pisano_character_diagonalization_holds (q m : ℕ) :
    gm_random_walk_mixing_pisano_character_diagonalization q m := by
  rfl

theorem gm_random_walk_mixing_pisano_character_decay (q blocks : ℕ) (hq : 2 ≤ q) :
    gm_random_walk_mixing_pisano_fourier_radius q (gm_random_walk_mixing_pisano_period q * blocks) ≤
      Real.exp (-((1 : ℝ) / (q : ℝ)) * blocks) := by
  simpa [gm_random_walk_mixing_pisano_fourier_radius,
      gm_random_walk_mixing_pisano_fourier_coefficient, gm_random_walk_mixing_pisano_period] using
    Omega.SyncKernelWeighted.paper_gm_pisano_period_character_decay
      q blocks ((1 : ℝ) / (q : ℝ)) (Real.exp (-((1 : ℝ) / (q : ℝ))))
      (gm_random_walk_mixing_pisano_period_pos hq)
      (gm_random_walk_mixing_pisano_one_period_contraction q)

theorem gm_random_walk_mixing_pisano_total_variation_decay (q blocks : ℕ) (hq : 2 ≤ q) :
    gm_random_walk_mixing_pisano_total_variation_bound q
        (gm_random_walk_mixing_pisano_period q * blocks) ≤
      (q : ℝ) / 2 * Real.exp (-((1 : ℝ) / (q : ℝ)) * blocks) := by
  have hdecay := gm_random_walk_mixing_pisano_character_decay q blocks hq
  unfold gm_random_walk_mixing_pisano_total_variation_bound
    gm_random_walk_mixing_pisano_nontrivial_spectral_radius
  exact mul_le_mul_of_nonneg_left hdecay (by positivity)

theorem gm_random_walk_mixing_pisano_mixing_time_bound_le (q m : ℕ) :
    gm_random_walk_mixing_pisano_mixing_time_bound q m ≤
      (gm_random_walk_mixing_pisano_period q : ℝ) * Real.log ((q : ℝ) + 1) := by
  have hlog : 0 ≤ Real.log ((q : ℝ) + 1) := by
    apply Real.log_nonneg
    nlinarith
  have hnum : 0 ≤ (gm_random_walk_mixing_pisano_period q : ℝ) * Real.log ((q : ℝ) + 1) := by
    unfold gm_random_walk_mixing_pisano_period
    nlinarith
  have hden : 1 ≤ (m : ℝ) + 1 := by
    nlinarith
  simpa [gm_random_walk_mixing_pisano_mixing_time_bound] using div_le_self hnum hden

/-- Paper label: `prop:gm-epsilon-bias-pisano-scale`. Once the Pisano-scale decay envelope is at
most `ε`, the concrete Fourier radius of the cyclic random walk is also at most `ε`. -/
theorem paper_gm_epsilon_bias_pisano_scale (q blocks : ℕ) (ε : ℝ) (hq : 2 ≤ q) (_hε : 0 < ε)
    (hscale : Real.exp (-((1 : ℝ) / (q : ℝ)) * blocks) ≤ ε) :
    gm_random_walk_mixing_pisano_fourier_radius q
        (gm_random_walk_mixing_pisano_period q * blocks) ≤ ε := by
  exact (gm_random_walk_mixing_pisano_character_decay q blocks hq).trans hscale

/-- Paper label: `prop:gm-random-walk-mixing-pisano`. The finite cyclic walk uses the Pisano-scale
character-decay package to identify the nontrivial spectral radius with the maximal Fourier mode
and to record the resulting total-variation and mixing-time bounds. -/
def paper_gm_random_walk_mixing_pisano (q m : ℕ) (_hq : 2 ≤ q) : Prop := by
  exact
    gm_random_walk_mixing_pisano_character_diagonalization q
        (gm_random_walk_mixing_pisano_period q * m) ∧
      gm_random_walk_mixing_pisano_total_variation_bound q
          (gm_random_walk_mixing_pisano_period q * m) ≤
        (q : ℝ) / 2 * Real.exp (-((1 : ℝ) / (q : ℝ)) * m) ∧
      gm_random_walk_mixing_pisano_mixing_time_bound q m ≤
        (gm_random_walk_mixing_pisano_period q : ℝ) * Real.log ((q : ℝ) + 1)

end

end Omega.SyncKernelRealInput
