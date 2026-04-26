import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

noncomputable section

open Matrix

/-- The golden ratio appearing in the Parry closed forms. -/
def goldenRatio : ℝ := (1 + Real.sqrt 5) / 2

private lemma goldenRatio_sq : goldenRatio ^ 2 = goldenRatio + 1 := by
  unfold goldenRatio
  have hs : (Real.sqrt 5) ^ 2 = 5 := by
    rw [Real.sq_sqrt]
    positivity
  nlinarith

private lemma goldenRatio_pos : 0 < goldenRatio := by
  unfold goldenRatio
  positivity

private lemma goldenRatio_ne_zero : goldenRatio ≠ 0 :=
  ne_of_gt goldenRatio_pos

/-- Helper for explicit `Fin 3` vectors. -/
def fin3Tuple {α : Type*} (a₀ a₁ a₂ : α) : Fin 3 → α := fun i =>
  match i.1 with
  | 0 => a₀
  | 1 => a₁
  | _ => a₂

/-- The three sum symbols `0,1,2`. -/
abbrev SumState := Fin 3

/-- The forbidden length-two words in the digitwise-sum image shift. -/
def real_input_digitwise_sum_sft_forbidden (i j : SumState) : Prop :=
  (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) ∨ (i = 2 ∧ j = 2)

/-- The adjacency matrix of the three-state SFT obtained from the forbidden-word analysis. -/
def real_input_digitwise_sum_sft_adjacency : Matrix SumState SumState ℚ :=
  !![(1 : ℚ), 1, 1;
    1, 1, 0;
    1, 0, 0]

/-- The zeta denominator matrix `I - z A_sum`. -/
def real_input_digitwise_sum_sft_zetaMatrix (z : ℚ) : Matrix SumState SumState ℚ :=
  !![(1 - z : ℚ), -z, -z;
    -z, 1 - z, 0;
    -z, 0, 1]

/-- Concrete tag for the digitwise-sum pushforward of the golden-mean Parry chain. -/
def digitwiseSumParryData : Unit := ()

/-- Closed-form transition law from the 3-case analysis of the current sum symbol. -/
def T_sum : SumState → SumState → ℝ := fun i =>
  match i.1 with
  | 0 => fin3Tuple (1 / goldenRatio ^ 2) (2 / goldenRatio ^ 3) (1 / goldenRatio ^ 4)
  | 1 => fin3Tuple (1 / goldenRatio) (1 / goldenRatio ^ 2) 0
  | _ => fin3Tuple 1 0 0

/-- Closed-form stationary weights of the digitwise-sum chain. -/
def pi_sum : SumState → ℝ :=
  fin3Tuple
    ((goldenRatio ^ 2 / (goldenRatio ^ 2 + 1)) ^ 2)
    ((2 * goldenRatio ^ 2) / (goldenRatio ^ 2 + 1) ^ 2)
    (1 / (goldenRatio ^ 2 + 1) ^ 2)

/-- A concrete finite-state Markov certificate: nonnegative rows summing to `1`. -/
def IsMarkovChain (_data : Unit) (T : SumState → SumState → ℝ) : Prop :=
  (∀ i j, 0 ≤ T i j) ∧
    (∀ i, T i 0 + T i 1 + T i 2 = 1)

/-- A concrete stationarity certificate for the three-state law. -/
def IsStationaryDistribution (π : SumState → ℝ) (T : SumState → SumState → ℝ) : Prop :=
  (∀ i, 0 ≤ π i) ∧
    (π 0 + π 1 + π 2 = 1) ∧
    (π 0 * T 0 0 + π 1 * T 1 0 + π 2 * T 2 0 = π 0) ∧
    (π 0 * T 0 1 + π 1 * T 1 1 + π 2 * T 2 1 = π 1) ∧
    (π 0 * T 0 2 + π 1 * T 1 2 + π 2 * T 2 2 = π 2)

private lemma row0_sum :
    T_sum 0 0 + T_sum 0 1 + T_sum 0 2 = 1 := by
  simp [T_sum, fin3Tuple]
  field_simp [goldenRatio_ne_zero]
  nlinarith [goldenRatio_sq]

private lemma row1_sum :
    T_sum 1 0 + T_sum 1 1 + T_sum 1 2 = 1 := by
  simp [T_sum, fin3Tuple]
  field_simp [goldenRatio_ne_zero]
  nlinarith [goldenRatio_sq]

private lemma row2_sum :
    T_sum 2 0 + T_sum 2 1 + T_sum 2 2 = 1 := by
  simp [T_sum, fin3Tuple]

private lemma pi_sum_total :
    pi_sum 0 + pi_sum 1 + pi_sum 2 = 1 := by
  simp [pi_sum, fin3Tuple]
  field_simp [goldenRatio_ne_zero]
  nlinarith [goldenRatio_sq]

private lemma stationary0 :
    pi_sum 0 * T_sum 0 0 + pi_sum 1 * T_sum 1 0 + pi_sum 2 * T_sum 2 0 = pi_sum 0 := by
  simp [T_sum, pi_sum, fin3Tuple]
  field_simp [goldenRatio_ne_zero]
  nlinarith [goldenRatio_sq]

private lemma stationary1 :
    pi_sum 0 * T_sum 0 1 + pi_sum 1 * T_sum 1 1 + pi_sum 2 * T_sum 2 1 = pi_sum 1 := by
  simp [T_sum, pi_sum, fin3Tuple]
  field_simp [goldenRatio_ne_zero]
  nlinarith [goldenRatio_sq]

private lemma stationary2 :
    pi_sum 0 * T_sum 0 2 + pi_sum 1 * T_sum 1 2 + pi_sum 2 * T_sum 2 2 = pi_sum 2 := by
  simp [T_sum, pi_sum, fin3Tuple]
  field_simp [goldenRatio_ne_zero]

private lemma real_input_digitwise_sum_sft_tsum_zero_iff (i j : SumState) :
    T_sum i j = 0 ↔ real_input_digitwise_sum_sft_forbidden i j := by
  fin_cases i <;> fin_cases j <;>
    simp [T_sum, fin3Tuple, real_input_digitwise_sum_sft_forbidden, goldenRatio_ne_zero]

private lemma real_input_digitwise_sum_sft_adjacency_zero_iff (i j : SumState) :
    real_input_digitwise_sum_sft_adjacency i j = 0 ↔ real_input_digitwise_sum_sft_forbidden i j := by
  fin_cases i <;> fin_cases j <;>
    simp [real_input_digitwise_sum_sft_adjacency, real_input_digitwise_sum_sft_forbidden]

private lemma real_input_digitwise_sum_sft_zeta_det (z : ℚ) :
    (real_input_digitwise_sum_sft_zetaMatrix z).det = 1 - 2 * z - z ^ 2 + z ^ 3 := by
  simp [real_input_digitwise_sum_sft_zetaMatrix, Matrix.det_fin_three]
  ring

/-- Paper label: `prop:real-input-digitwise-sum-sft`. -/
theorem paper_real_input_digitwise_sum_sft :
    (∀ i j : SumState, T_sum i j = 0 ↔ real_input_digitwise_sum_sft_forbidden i j) ∧
      (∀ i j : SumState,
        real_input_digitwise_sum_sft_adjacency i j = 0 ↔
          real_input_digitwise_sum_sft_forbidden i j) ∧
      (∀ z : ℚ,
        (real_input_digitwise_sum_sft_zetaMatrix z).det = 1 - 2 * z - z ^ 2 + z ^ 3) := by
  refine ⟨real_input_digitwise_sum_sft_tsum_zero_iff, ?_, real_input_digitwise_sum_sft_zeta_det⟩
  exact real_input_digitwise_sum_sft_adjacency_zero_iff

/-- Paper label: `prop:real-input-digitwise-sum-parry-markov`. -/
theorem paper_real_input_digitwise_sum_parry_markov :
    IsMarkovChain digitwiseSumParryData T_sum ∧ IsStationaryDistribution pi_sum T_sum := by
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro i j
      have hφ : 0 < goldenRatio := goldenRatio_pos
      fin_cases i <;> fin_cases j <;> simp [T_sum, fin3Tuple] <;> positivity
    · intro i
      fin_cases i
      · exact row0_sum
      · exact row1_sum
      · exact row2_sum
  · refine ⟨?_, pi_sum_total, stationary0, stationary1, stationary2⟩
    intro i
    fin_cases i <;> simp [pi_sum, fin3Tuple] <;> positivity

end

end Omega.SyncKernelWeighted
