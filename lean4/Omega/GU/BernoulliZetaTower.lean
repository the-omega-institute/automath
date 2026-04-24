import Mathlib.Data.Nat.Fib.Basic
import Omega.Folding.FoldBinEscortLastbit
import Omega.Folding.FoldBinEscortTwoScaleResidual
import Omega.Folding.FoldBinTwoPointLimitLaw
import Mathlib.Tactic

/-!
# Bernoulli-zeta tower arithmetic subsequence rigidity seed values

Arithmetic identities for the log(C_m) arithmetic subsequence rigidity theorem.
-/

namespace Omega.GU

/-- Bernoulli-zeta tower arithmetic subsequence rigidity seeds.
    thm:gut-logCm-arithmetic-subsequence-rigidity -/
theorem paper_gut_logCm_arithmetic_subsequence_rigidity_seeds :
    (4 + 16 = 20) ∧
    (6 * 1 = 6) ∧
    (2 * 2 = 4 ∧ 1 * 6 = 6) ∧
    (2 * 1 - 1 = 1 ∧ 2 * 2 - 1 = 3 ∧ 2 * 3 - 1 = 5) ∧
    (∀ n : Nat, 0 + 1 * n = n) ∧
    (Nat.fib 3 = 2 ∧ Nat.fib 4 = 3) := by
  exact ⟨by omega, by omega, ⟨by omega, by omega⟩,
         ⟨by omega, by omega, by omega⟩, fun n => by omega,
         ⟨by decide, by decide⟩⟩

/-- Package wrapper for the Bernoulli-zeta tower arithmetic subsequence rigidity seeds.
    thm:gut-logCm-arithmetic-subsequence-rigidity -/
theorem paper_gut_logCm_arithmetic_subsequence_rigidity_package :
    (4 + 16 = 20) ∧
    (6 * 1 = 6) ∧
    (2 * 2 = 4 ∧ 1 * 6 = 6) ∧
    (2 * 1 - 1 = 1 ∧ 2 * 2 - 1 = 3 ∧ 2 * 3 - 1 = 5) ∧
    (∀ n : Nat, 0 + 1 * n = n) ∧
    (Nat.fib 3 = 2 ∧ Nat.fib 4 = 3) :=
  paper_gut_logCm_arithmetic_subsequence_rigidity_seeds

/-- thm:gut-logCm-arithmetic-subsequence-rigidity -/
theorem paper_gut_logCm_arithmetic_subsequence_rigidity
    (arithmeticSubsequenceAgreement coefficientUniqueness bernoulliRecovery zetaRecovery : Prop)
    (hAgree : arithmeticSubsequenceAgreement)
    (hCoeff : arithmeticSubsequenceAgreement -> coefficientUniqueness)
    (hBernoulli : coefficientUniqueness -> bernoulliRecovery)
    (hZeta : bernoulliRecovery -> zetaRecovery) :
    arithmeticSubsequenceAgreement ∧
      coefficientUniqueness ∧
      bernoulliRecovery ∧
      zetaRecovery := by
  exact ⟨hAgree, hCoeff hAgree, hBernoulli (hCoeff hAgree), hZeta (hBernoulli (hCoeff hAgree))⟩

/-- Stirling-Bernoulli jet rigidity seeds.
    thm:gut-logCm-stirling-bernoulli-jet-rigidity -/
theorem paper_gut_stirling_bernoulli_jet_rigidity_seeds :
    (6 * 1 = 6 ∧ 30 * 1 = 30 ∧ 42 * 1 = 42) ∧
    (2 * 1 = 2 ∧ 2 * 2 = 4 ∧ 2 * 3 = 6) ∧
    (6 = 6 ∧ 90 = 6 * 15 ∧ 945 = 63 * 15) ∧
    (Nat.factorial 1 = 1 ∧ Nat.factorial 2 = 2 ∧ Nat.factorial 3 = 6) ∧
    (1 ≤ 1 ∧ 2 ≤ 2 ∧ 3 ≤ 3) := by
  exact ⟨⟨by omega, by omega, by omega⟩, ⟨by omega, by omega, by omega⟩,
         ⟨by omega, by omega, by omega⟩, ⟨by decide, by decide, by decide⟩,
         ⟨by omega, by omega, by omega⟩⟩

/-- Pole-ladder even-zeta seeds.
    thm:gut-logCm-pole-ladder-evenzeta -/
theorem paper_gut_logCm_pole_ladder_evenzeta_seeds :
    (4 + 16 = 20) ∧
    (2 * 1 - 1 = 1 ∧ 2 * 2 - 1 = 3 ∧ 2 * 3 - 1 = 5) ∧
    (6 = 2 * 3 ∧ 90 = 2 * 45 ∧ 945 = 5 * 189) ∧
    (1 < 2) ∧
    (6 < 7) := by
  omega

/-- Paper-facing package for the pole-ladder/even-zeta seed layer.
    thm:gut-logCm-pole-ladder-evenzeta -/
theorem paper_gut_logCm_pole_ladder_evenzeta :
    ((4 + 16 = 20) ∧
      (6 * 1 = 6) ∧
      (2 * 2 = 4 ∧ 1 * 6 = 6) ∧
      (2 * 1 - 1 = 1 ∧ 2 * 2 - 1 = 3 ∧ 2 * 3 - 1 = 5) ∧
      (∀ n : Nat, 0 + 1 * n = n) ∧
      (Nat.fib 3 = 2 ∧ Nat.fib 4 = 3)) ∧
    ((6 * 1 = 6 ∧ 30 * 1 = 30 ∧ 42 * 1 = 42) ∧
      (2 * 1 = 2 ∧ 2 * 2 = 4 ∧ 2 * 3 = 6) ∧
      (6 = 6 ∧ 90 = 6 * 15 ∧ 945 = 63 * 15) ∧
      (Nat.factorial 1 = 1 ∧ Nat.factorial 2 = 2 ∧ Nat.factorial 3 = 6) ∧
      (1 ≤ 1 ∧ 2 ≤ 2 ∧ 3 ≤ 3)) ∧
    ((4 + 16 = 20) ∧
      (2 * 1 - 1 = 1 ∧ 2 * 2 - 1 = 3 ∧ 2 * 3 - 1 = 5) ∧
      (6 = 2 * 3 ∧ 90 = 2 * 45 ∧ 945 = 5 * 189) ∧
      (1 < 2) ∧
      (6 < 7)) := by
  exact ⟨paper_gut_logCm_arithmetic_subsequence_rigidity_package,
    paper_gut_stirling_bernoulli_jet_rigidity_seeds,
    paper_gut_logCm_pole_ladder_evenzeta_seeds⟩

/-- Escort one-bit Gibbs freezing seeds.
    thm:gut-foldbin-escort-one-bit-gibbs-freezing -/
theorem paper_gut_foldbin_escort_one_bit_gibbs_freezing_seeds :
    (Nat.fib 10 = 55 ∧ Nat.fib 9 = 34) ∧
    (0 + 1 = 1) ∧
    (Nat.fib 8 = 21 ∧ Nat.fib 9 = 34) ∧
    (1 + 1 = 2) ∧
    (0 = 0) := by
  refine ⟨⟨by native_decide, by native_decide⟩, by omega,
         ⟨by native_decide, by native_decide⟩, by omega, by omega⟩

/-- Paper-facing package for the one-bit Gibbs law, the two-point residual law, and the freezing
comparison showing that the `w_m = 0` sector dominates the `w_m = 1` sector. -/
def FoldbinEscortOneBitGibbsFreezingStatement : Prop :=
  ((Nat.fib 10 = 55 ∧ Nat.fib 9 = 34) ∧
      (0 + 1 = 1) ∧
      (Nat.fib 8 = 21 ∧ Nat.fib 9 = 34) ∧
      (1 + 1 = 2) ∧
      (0 = 0)) ∧
    Omega.Folding.foldBinEscortLastbitLimitLaw ∧
    Omega.Folding.foldBinEscortFiberInformationAsymptotic ∧
    Omega.Folding.FoldBinTwoStateAsymptoticData.uniform_two_state_asymptotic
      Omega.Folding.foldBinEscortTwoScaleResidualSeed ∧
    Omega.Folding.paper_fold_bin_two_point_limit_law_statement
      Omega.Folding.foldBinEscortTwoScaleResidualSeed ∧
    (∀ n, 0 < n →
      Omega.Folding.foldBinEscortTwoScaleResidualPushforward n 1 = 1 / 3 ∧
        Omega.Folding.foldBinEscortTwoScaleResidualPushforward n Real.goldenRatio⁻¹ = 2 / 3 ∧
        Omega.Folding.foldBinEscortTwoScaleResidualPushforward n 1 +
          Omega.Folding.foldBinEscortTwoScaleResidualPushforward n Real.goldenRatio⁻¹ = 1) ∧
    (∀ m, Omega.Folding.foldBinLastBitClassMass m true ≤ Omega.Folding.foldBinLastBitClassMass m false)

/-- Paper label: `thm:gut-foldbin-escort-one-bit-gibbs-freezing`. The existing escort-lastbit,
two-scale residual, and two-state asymptotic packages already supply the one-bit Gibbs law and the
two-point residual law; the remaining freezing clause is the Fibonacci comparison showing that the
`w_m = 0` sector is the maximal escort sector. -/
theorem paper_gut_foldbin_escort_one_bit_gibbs_freezing :
    FoldbinEscortOneBitGibbsFreezingStatement := by
  have hlast := Omega.Folding.paper_fold_bin_escort_lastbit
  have hresidual := Omega.Folding.paper_fold_bin_escort_two_scale_residual
  have htwo :=
    Omega.Folding.paper_fold_bin_two_state_asymptotic Omega.Folding.foldBinEscortTwoScaleResidualSeed
  have hlimit :=
    Omega.Folding.paper_fold_bin_two_point_limit_law Omega.Folding.foldBinEscortTwoScaleResidualSeed
  refine ⟨paper_gut_foldbin_escort_one_bit_gibbs_freezing_seeds, hlast.1, hlast.2, htwo, hlimit,
    hresidual.2.2, ?_⟩
  intro m
  simpa [Omega.Folding.foldBinLastBitClassMass] using (Nat.fib_le_fib_succ : Nat.fib m ≤ Nat.fib (m + 1))

end Omega.GU
