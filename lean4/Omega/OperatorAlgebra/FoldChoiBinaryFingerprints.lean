import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.OperatorAlgebra.FoldChoiMaxeigApproxSATHard
import Omega.OperatorAlgebra.FoldQuantumChannelChoiRenyiMoments

namespace Omega.OperatorAlgebra

noncomputable section

/-- The binary Choi block model attached to the SAT fold: one block in the unsatisfiable case, two
blocks in the satisfiable case. -/
def fold_choi_binary_fingerprints_environment {n : ℕ} (φ : BitVec n → Bool) :
    FoldQuantumChannelEnvironmentData :=
  let N := satFoldAmbientSize n
  let s := satWitnessCount φ
  if _hs : s = 0 then
    { blockRanks := [N] }
  else
    { blockRanks := [s, N - s] }

/-- The `D_max` expression read from the maximal Choi eigenvalue against the maximally mixed
reference state `I / N²`. -/
def fold_choi_binary_fingerprints_dmax {n : ℕ} (φ : BitVec n → Bool) : ℝ :=
  let N := satFoldAmbientSize n
  Real.log ((N : ℝ) ^ 2 * (satFoldNormalizedChoiMaxEig φ : ℝ))

/-- The binary Choi purity `Tr ρ²` coming from the corresponding block model. -/
def fold_choi_binary_fingerprints_purity {n : ℕ} (φ : BitVec n → Bool) : ℝ :=
  (fold_choi_binary_fingerprints_environment φ).choiPurity

theorem fold_choi_binary_fingerprints_satWitnessCount_eq_zero_iff {n : ℕ} (φ : BitVec n → Bool) :
    satWitnessCount φ = 0 ↔ ¬ satisfiable φ := by
  constructor
  · intro hs hsat
    rcases hsat with ⟨w, hw⟩
    have hpos : 0 < satWitnessCount φ := by
      unfold satWitnessCount
      exact Fintype.card_pos_iff.mpr ⟨⟨w, hw⟩⟩
    omega
  · intro hns
    unfold satWitnessCount
    letI : IsEmpty {w : BitVec n // φ w = true} := by
      refine ⟨?_⟩
      intro x
      exact hns ⟨x.1, x.2⟩
    simp

theorem fold_choi_binary_fingerprints_satWitnessCount_le_half_ambient
    {n : ℕ} (φ : BitVec n → Bool) :
    satWitnessCount φ ≤ satFoldAmbientSize n / 2 := by
  have hcard : satWitnessCount φ ≤ Fintype.card (BitVec n) := by
    unfold satWitnessCount
    exact Fintype.card_subtype_le (fun w : BitVec n => φ w = true)
  have hbit : Fintype.card (BitVec n) = 2 ^ n := by
    simp [BitVec]
  have hhalf : satFoldAmbientSize n / 2 = 2 ^ n := by
    unfold satFoldAmbientSize
    rw [Nat.pow_succ', Nat.mul_comm, Nat.mul_div_left _ (by decide : 0 < 2)]
  rw [hhalf]
  exact hcard.trans_eq hbit

theorem fold_choi_binary_fingerprints_single_block_purity
    (N : ℕ) (hN : 0 < N) :
    ({ blockRanks := [N] } : FoldQuantumChannelEnvironmentData).choiPurity =
      1 / (N : ℝ) ^ 2 := by
  have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  rw [(paper_op_algebra_fold_quantum_channel_choi_renyi_moments
      ({ blockRanks := [N] } : FoldQuantumChannelEnvironmentData) 2).2.2.2.1]
  simp [FoldQuantumChannelEnvironmentData.choiRenyiPowerSum,
    FoldQuantumChannelEnvironmentData.choiBlockRenyiMass,
    FoldQuantumChannelEnvironmentData.choiBlockEigenvalue,
    FoldQuantumChannelEnvironmentData.totalInputDim]
  field_simp [hNne]

theorem fold_choi_binary_fingerprints_two_block_purity
    (N s : ℕ) (hs : 0 < s) (hsle : s ≤ N / 2) :
    ({ blockRanks := [s, N - s] } : FoldQuantumChannelEnvironmentData).choiPurity =
      2 / (N : ℝ) ^ 2 := by
  have hNpos : 0 < N := by omega
  have hNminus : 0 < N - s := by omega
  have hsle' : s ≤ N := by omega
  have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hNpos
  have hsne : (s : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hs
  have hNminusne : ((N - s : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hNminus
  rw [(paper_op_algebra_fold_quantum_channel_choi_renyi_moments
      ({ blockRanks := [s, N - s] } : FoldQuantumChannelEnvironmentData) 2).2.2.2.1]
  simp [FoldQuantumChannelEnvironmentData.choiRenyiPowerSum,
    FoldQuantumChannelEnvironmentData.choiBlockRenyiMass,
    FoldQuantumChannelEnvironmentData.choiBlockEigenvalue,
    FoldQuantumChannelEnvironmentData.totalInputDim]
  field_simp [hNne, hsne, hNminusne]
  have hsub : (((N - s : ℕ) : ℝ)) = (N : ℝ) - s := by
    rw [Nat.cast_sub hsle']
  have hsum : (N : ℝ) = s + ((N - s : ℕ) : ℝ) := by
    nlinarith [hsub]
  nlinarith

theorem fold_choi_binary_fingerprints_dmax_lower_bound
    {n : ℕ} {φ : BitVec n → Bool} (hsat : satisfiable φ) :
    2 ≤ ((satFoldAmbientSize n : ℝ) ^ 2) * (satFoldNormalizedChoiMaxEig φ : ℝ) := by
  let N := satFoldAmbientSize n
  let s := satWitnessCount φ
  have hsne_nat : s ≠ 0 := by
    intro hs
    exact (fold_choi_binary_fingerprints_satWitnessCount_eq_zero_iff φ).1 hs hsat
  have hspos : 0 < s := Nat.pos_iff_ne_zero.mpr hsne_nat
  have hsle : s ≤ N / 2 := fold_choi_binary_fingerprints_satWitnessCount_le_half_ambient φ
  have hmin : Nat.min s (N - s) = s := by
    apply Nat.min_eq_left
    omega
  have hNpos : 0 < N := by
    dsimp [N, satFoldAmbientSize]
    positivity
  have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hNpos
  have hsne : (s : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hspos
  have harg :
      ((N : ℝ) ^ 2) * (satFoldNormalizedChoiMaxEig φ : ℝ) =
        (N : ℝ) / s := by
    rw [(paper_fold_choi_maxeig_approx_sat_hard n φ).2 hsat]
    rw [hmin]
    norm_num [N]
    field_simp [hNne, hsne]
  rw [harg]
  have hspos_real : 0 < (s : ℝ) := by exact_mod_cast hspos
  have hineq : (2 : ℝ) * s ≤ N := by
    exact_mod_cast (show 2 * s ≤ N by omega)
  exact (le_div_iff₀ hspos_real).2 hineq

/-- Paper-facing corollary combining the SAT-hard Choi maximal-eigenvalue theorem with the
blockwise Choi purity formulas. -/
theorem paper_fold_choi_binary_fingerprints
    (n : ℕ) (φ : BitVec n → Bool) :
    ((¬ satisfiable φ) →
      fold_choi_binary_fingerprints_dmax φ = 0 ∧
        fold_choi_binary_fingerprints_purity φ = 1 / (satFoldAmbientSize n : ℝ) ^ 2) ∧
      (satisfiable φ →
        Real.log 2 ≤ fold_choi_binary_fingerprints_dmax φ ∧
          fold_choi_binary_fingerprints_purity φ = 2 / (satFoldAmbientSize n : ℝ) ^ 2) := by
  let N := satFoldAmbientSize n
  refine ⟨?_, ?_⟩
  · intro hunsat
    have hs : satWitnessCount φ = 0 :=
      (fold_choi_binary_fingerprints_satWitnessCount_eq_zero_iff φ).2 hunsat
    have hNpos : 0 < N := by
      dsimp [N, satFoldAmbientSize]
      positivity
    constructor
    · unfold fold_choi_binary_fingerprints_dmax
      rw [(paper_fold_choi_maxeig_approx_sat_hard n φ).1 hunsat]
      have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hNpos
      have hone : (N : ℝ) ^ 2 * (1 / (N : ℝ) ^ 2) = 1 := by
        field_simp [hNne]
      simpa [N, Real.log_one] using congrArg Real.log hone
    · unfold fold_choi_binary_fingerprints_purity fold_choi_binary_fingerprints_environment
      simp [N, hs, fold_choi_binary_fingerprints_single_block_purity N hNpos]
  · intro hsat
    have hs : satWitnessCount φ ≠ 0 := by
      intro hs
      exact (fold_choi_binary_fingerprints_satWitnessCount_eq_zero_iff φ).1 hs hsat
    have hspos : 0 < satWitnessCount φ := Nat.pos_iff_ne_zero.mpr hs
    have hsle :
        satWitnessCount φ ≤ N / 2 :=
      fold_choi_binary_fingerprints_satWitnessCount_le_half_ambient φ
    constructor
    · unfold fold_choi_binary_fingerprints_dmax
      have hbound := fold_choi_binary_fingerprints_dmax_lower_bound hsat
      simpa [N] using Real.log_le_log (by norm_num) hbound
    · unfold fold_choi_binary_fingerprints_purity fold_choi_binary_fingerprints_environment
      simp [N, hs, fold_choi_binary_fingerprints_two_block_purity N (satWitnessCount φ) hspos hsle]

end
end Omega.OperatorAlgebra
