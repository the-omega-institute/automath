import Mathlib.Data.Finset.Max
import Mathlib.Tactic
import Omega.EA.ChiLayeredFiberSpectrumRecovery

namespace Omega.EA

open scoped BigOperators

/-- Concrete data for extracting the maximal Watatani fiber and its chi-sector fingerprint from the
signed `Z2 x Z2` moment package. -/
structure fold_indw_high_q_extract_maxfiber_and_chi_data where
  m : Nat
  d : Z2x2Character → Nat
  hmass : Finset.univ.sum d = 2 ^ m

/-- The maximal block size in the four chi-sectors. -/
def fold_indw_high_q_extract_maxfiber_and_chi_maxfiber
    (D : fold_indw_high_q_extract_maxfiber_and_chi_data) : Nat :=
  Finset.univ.sup D.d

/-- The signed-moment reconstruction recovers every sector size, and one chi-sector attains the
maximal fiber. -/
def fold_indw_high_q_extract_maxfiber_and_chi_statement
    (D : fold_indw_high_q_extract_maxfiber_and_chi_data) : Prop :=
  (∀ chi : Z2x2Character, recoverSectorBlockSizeFromSignedMoments D.m D.d chi = (D.d chi : ℚ)) ∧
    (∀ chi : Z2x2Character, recoverSectorPowerSumFromSignedMoments D.m D.d chi 1 = (D.d chi : ℚ)) ∧
    (∃ chiMax : Z2x2Character,
      D.d chiMax = fold_indw_high_q_extract_maxfiber_and_chi_maxfiber D) ∧
    ∀ chi : Z2x2Character, D.d chi ≤ fold_indw_high_q_extract_maxfiber_and_chi_maxfiber D

private theorem fold_indw_high_q_extract_maxfiber_and_chi_recover_sector_block_size_eq
    (D : fold_indw_high_q_extract_maxfiber_and_chi_data) (chi : Z2x2Character) :
    recoverSectorBlockSizeFromSignedMoments D.m D.d chi = sectorPowerSumFromBlockSizes D.d chi 1 := by
  have hpow_ne : (2 ^ D.m : ℚ) ≠ 0 := by positivity
  have _ := paper_fold_groupoid_z2x2_joint_spectral_measure D.m D.d D.hmass
  cases chi with
  | mk a b =>
      cases a <;> cases b <;>
        simp [recoverSectorBlockSizeFromSignedMoments, signedMomentTrace, normalizedBlockTrace,
          sectorPowerSumFromBlockSizes, scanEigenvalue, revEigenvalue, signOfBool,
          Fintype.sum_prod_type, Fin.sum_univ_two, div_eq_mul_inv] <;>
        field_simp [hpow_ne] <;>
        ring

/-- Paper label: `cor:fold-indw-high-q-extract-maxfiber-and-chi`. -/
theorem paper_fold_indw_high_q_extract_maxfiber_and_chi
    (D : fold_indw_high_q_extract_maxfiber_and_chi_data) :
    fold_indw_high_q_extract_maxfiber_and_chi_statement D := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro chi
    simpa [sectorPowerSumFromBlockSizes] using
      fold_indw_high_q_extract_maxfiber_and_chi_recover_sector_block_size_eq D chi
  · intro chi
    simp [recoverSectorPowerSumFromSignedMoments,
      fold_indw_high_q_extract_maxfiber_and_chi_recover_sector_block_size_eq,
      sectorPowerSumFromBlockSizes]
  · obtain ⟨chiMax, _, hchiMax⟩ :=
      Finset.exists_mem_eq_sup (s := Finset.univ) ⟨(true, true), by simp⟩ D.d
    refine ⟨chiMax, ?_⟩
    simpa [fold_indw_high_q_extract_maxfiber_and_chi_maxfiber] using hchiMax.symm
  · intro chi
    simpa [fold_indw_high_q_extract_maxfiber_and_chi_maxfiber] using
      (Finset.le_sup (f := D.d) (by simp : chi ∈ Finset.univ))

end Omega.EA
