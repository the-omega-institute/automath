import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic
import Omega.FoldResidualTime.Window6FixedFreezingLaw

namespace Omega.Zeta

/-- Window-6 finite partition function for the multiplicity histogram `(2:8, 3:4, 4:9)`. -/
def xi_time_part9ze_positive_zero_temperature_freezing_window6Partition (q : ℕ) : ℝ :=
  8 * (2 : ℝ) ^ q + 4 * (3 : ℝ) ^ q + 9 * (4 : ℝ) ^ q

/-- Maximal-shell normalization of the window-6 partition function. -/
noncomputable def xi_time_part9ze_positive_zero_temperature_freezing_window6Normalized
    (q : ℕ) : ℝ :=
  xi_time_part9ze_positive_zero_temperature_freezing_window6Partition q / (4 : ℝ) ^ q

/-- The lower multiplicity shells after factoring out the maximal `4^q` layer. -/
noncomputable def xi_time_part9ze_positive_zero_temperature_freezing_lowerShells
    (q : ℕ) : ℝ :=
  4 * (3 / 4 : ℝ) ^ q + 8 * (1 / 2 : ℝ) ^ q

/-- Positive zero-temperature concentration on the maximal window-6 shell. -/
def xi_time_part9ze_positive_zero_temperature_freezing_positiveZeroTemperatureLimit : Prop :=
  Filter.Tendsto xi_time_part9ze_positive_zero_temperature_freezing_lowerShells
    Filter.atTop (nhds 0) ∧
    Filter.Tendsto xi_time_part9ze_positive_zero_temperature_freezing_window6Normalized
      Filter.atTop (nhds 9)

/-- Closed form for the window-6 histogram partition and its normalized factorization. -/
def xi_time_part9ze_positive_zero_temperature_freezing_window6ClosedForm : Prop :=
  ∀ q : ℕ,
    xi_time_part9ze_positive_zero_temperature_freezing_window6Partition q =
        8 * (2 : ℝ) ^ q + 4 * (3 : ℝ) ^ q + 9 * (4 : ℝ) ^ q ∧
      xi_time_part9ze_positive_zero_temperature_freezing_window6Partition q =
        (4 : ℝ) ^ q *
          (9 + 4 * (3 / 4 : ℝ) ^ q + 8 * (1 / 2 : ℝ) ^ q) ∧
      xi_time_part9ze_positive_zero_temperature_freezing_window6Normalized q =
        9 + xi_time_part9ze_positive_zero_temperature_freezing_lowerShells q

lemma xi_time_part9ze_positive_zero_temperature_freezing_partition_factorization (q : ℕ) :
    xi_time_part9ze_positive_zero_temperature_freezing_window6Partition q =
      (4 : ℝ) ^ q * (9 + 4 * (3 / 4 : ℝ) ^ q + 8 * (1 / 2 : ℝ) ^ q) := by
  unfold xi_time_part9ze_positive_zero_temperature_freezing_window6Partition
  calc
    8 * (2 : ℝ) ^ q + 4 * (3 : ℝ) ^ q + 9 * (4 : ℝ) ^ q
        = 9 * (4 : ℝ) ^ q + 4 * ((4 : ℝ) ^ q * (3 / 4 : ℝ) ^ q) +
            8 * ((4 : ℝ) ^ q * (1 / 2 : ℝ) ^ q) := by
            rw [← mul_pow, ← mul_pow]
            norm_num
            ring
    _ = (4 : ℝ) ^ q * (9 + 4 * (3 / 4 : ℝ) ^ q + 8 * (1 / 2 : ℝ) ^ q) := by
          ring

lemma xi_time_part9ze_positive_zero_temperature_freezing_normalized_eq (q : ℕ) :
    xi_time_part9ze_positive_zero_temperature_freezing_window6Normalized q =
      9 + xi_time_part9ze_positive_zero_temperature_freezing_lowerShells q := by
  unfold xi_time_part9ze_positive_zero_temperature_freezing_window6Normalized
    xi_time_part9ze_positive_zero_temperature_freezing_lowerShells
  rw [xi_time_part9ze_positive_zero_temperature_freezing_partition_factorization]
  have hpow : ((4 : ℝ) ^ q) ≠ 0 := pow_ne_zero q (by norm_num)
  field_simp [hpow]
  ring

lemma xi_time_part9ze_positive_zero_temperature_freezing_lowerShells_tendsto :
    Filter.Tendsto xi_time_part9ze_positive_zero_temperature_freezing_lowerShells
      Filter.atTop (nhds 0) := by
  have hthreeFourths :
      Filter.Tendsto (fun q : ℕ => (3 / 4 : ℝ) ^ q) Filter.atTop (nhds 0) := by
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num)
  have hhalf :
      Filter.Tendsto (fun q : ℕ => (1 / 2 : ℝ) ^ q) Filter.atTop (nhds 0) := by
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num)
  have h3 :
      Filter.Tendsto (fun q : ℕ => (4 : ℝ) * (3 / 4 : ℝ) ^ q)
        Filter.atTop (nhds ((4 : ℝ) * 0)) :=
    tendsto_const_nhds.mul hthreeFourths
  have h2 :
      Filter.Tendsto (fun q : ℕ => (8 : ℝ) * (1 / 2 : ℝ) ^ q)
        Filter.atTop (nhds ((8 : ℝ) * 0)) :=
    tendsto_const_nhds.mul hhalf
  have hmain :
      Filter.Tendsto
        (fun q : ℕ => (4 : ℝ) * (3 / 4 : ℝ) ^ q + (8 : ℝ) * (1 / 2 : ℝ) ^ q)
        Filter.atTop (nhds 0) := by
    simpa using h3.add h2
  have heq :
      xi_time_part9ze_positive_zero_temperature_freezing_lowerShells =
        fun q : ℕ => (4 : ℝ) * (3 / 4 : ℝ) ^ q + (8 : ℝ) * (1 / 2 : ℝ) ^ q := by
    funext q
    simp [xi_time_part9ze_positive_zero_temperature_freezing_lowerShells]
  exact Filter.Tendsto.congr' (Filter.Eventually.of_forall fun q => by simp [heq]) hmain

lemma xi_time_part9ze_positive_zero_temperature_freezing_normalized_tendsto :
    Filter.Tendsto xi_time_part9ze_positive_zero_temperature_freezing_window6Normalized
      Filter.atTop (nhds 9) := by
  have hsum :
      Filter.Tendsto
        (fun q : ℕ => (9 : ℝ) + xi_time_part9ze_positive_zero_temperature_freezing_lowerShells q)
        Filter.atTop (nhds ((9 : ℝ) + 0)) :=
    tendsto_const_nhds.add
      xi_time_part9ze_positive_zero_temperature_freezing_lowerShells_tendsto
  have heq :
      xi_time_part9ze_positive_zero_temperature_freezing_window6Normalized =ᶠ[Filter.atTop]
        fun q : ℕ => (9 : ℝ) +
          xi_time_part9ze_positive_zero_temperature_freezing_lowerShells q :=
    Filter.Eventually.of_forall
      xi_time_part9ze_positive_zero_temperature_freezing_normalized_eq
  simpa using Filter.Tendsto.congr' heq.symm hsum

/-- Paper label: `thm:xi-time-part9ze-positive-zero-temperature-freezing`. -/
theorem paper_xi_time_part9ze_positive_zero_temperature_freezing :
    xi_time_part9ze_positive_zero_temperature_freezing_positiveZeroTemperatureLimit ∧
      xi_time_part9ze_positive_zero_temperature_freezing_window6ClosedForm := by
  refine
    ⟨⟨xi_time_part9ze_positive_zero_temperature_freezing_lowerShells_tendsto,
        xi_time_part9ze_positive_zero_temperature_freezing_normalized_tendsto⟩, ?_⟩
  intro q
  exact
    ⟨rfl, xi_time_part9ze_positive_zero_temperature_freezing_partition_factorization q,
      xi_time_part9ze_positive_zero_temperature_freezing_normalized_eq q⟩

end Omega.Zeta
