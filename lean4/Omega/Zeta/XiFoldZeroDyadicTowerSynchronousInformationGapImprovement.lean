import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic
import Omega.Conclusion.FoldZeroPacketSynchronousVisibleSuppression

namespace Omega.Zeta

/-- The dyadic-tower zero-count contribution `\Xi_m`. -/
def xi_fold_zero_dyadic_tower_synchronous_information_gap_improvement_Xi (m : Nat) : Nat :=
  Nat.fib ((m + 2) / 2)

/-- The fold-zero dyadic-tower lower bound improves the four standard synchronous uncertainty
envelopes when substituted into the zero-packet formulas. -/
def xi_fold_zero_dyadic_tower_synchronous_information_gap_improvement_statement
    (m : Nat) : Prop :=
  let M := (Nat.fib (m + 3) : ℝ)
  let Xi := (xi_fold_zero_dyadic_tower_synchronous_information_gap_improvement_Xi m : ℝ)
  Omega.Conclusion.zeroPacketCollisionUpperBound M Xi ≤
      Omega.Conclusion.zeroPacketCollisionUpperBound M 0 ∧
    Omega.Conclusion.zeroPacketMaxfiberUpperBound m M Xi ≤
      Omega.Conclusion.zeroPacketMaxfiberUpperBound m M 0 ∧
    Omega.Conclusion.zeroPacketEntropyGapUpperBound M Xi ≤
      Omega.Conclusion.zeroPacketEntropyGapUpperBound M 0 ∧
    Omega.Conclusion.zeroPacketFourierUpperBound m M Xi ≤
      Omega.Conclusion.zeroPacketFourierUpperBound m M 0 ∧
    (m = 58 →
      xi_fold_zero_dyadic_tower_synchronous_information_gap_improvement_Xi m = 832040 ∧
        Nat.fib 30 + Nat.fib 31 = Nat.fib 32)

private lemma xi_fold_zero_dyadic_tower_synchronous_information_gap_improvement_xi_le_main
    (m : Nat) :
    xi_fold_zero_dyadic_tower_synchronous_information_gap_improvement_Xi m ≤ Nat.fib (m + 2) := by
  unfold xi_fold_zero_dyadic_tower_synchronous_information_gap_improvement_Xi
  exact Nat.fib_mono (by omega)

private lemma xi_fold_zero_dyadic_tower_synchronous_information_gap_improvement_main_pos
    (m : Nat) : 0 < (Nat.fib (m + 3) : ℝ) := by
  exact_mod_cast Nat.fib_pos.mpr (by omega)

private lemma xi_fold_zero_dyadic_tower_synchronous_information_gap_improvement_gap_pos
    (m : Nat) :
    0 <
      (Nat.fib (m + 3) : ℝ) -
        xi_fold_zero_dyadic_tower_synchronous_information_gap_improvement_Xi m := by
  have hXi_le_nat :
      xi_fold_zero_dyadic_tower_synchronous_information_gap_improvement_Xi m ≤ Nat.fib (m + 2) :=
    xi_fold_zero_dyadic_tower_synchronous_information_gap_improvement_xi_le_main m
  have hXi_le :
      (xi_fold_zero_dyadic_tower_synchronous_information_gap_improvement_Xi m : ℝ) ≤
        Nat.fib (m + 2) := by
    exact_mod_cast hXi_le_nat
  have hfib_nat : Nat.fib (m + 3) = Nat.fib (m + 2) + Nat.fib (m + 1) := by
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using Nat.fib_add_two (n := m + 1)
  have hfib : (Nat.fib (m + 3) : ℝ) = Nat.fib (m + 2) + Nat.fib (m + 1) := by
    exact_mod_cast hfib_nat
  have htail : 0 < (Nat.fib (m + 1) : ℝ) := by
    exact_mod_cast Nat.fib_pos.mpr (by omega)
  linarith

/-- Paper label:
`thm:xi-fold-zero-dyadic-tower-synchronous-information-gap-improvement`. Defining
`\Xi_m = F_{\lfloor (m+2)/2 \rfloor}`, the dyadic-tower zero packet improves the collision,
max-fiber, entropy, and Fourier envelopes by direct substitution into the zero-packet bounds; for
`m = 58`, the specialization is the arithmetic identity `F_30 = 832040` together with the
Fibonacci sum `F_30 + F_31 = F_32`. -/
theorem paper_xi_fold_zero_dyadic_tower_synchronous_information_gap_improvement (m : Nat) :
    xi_fold_zero_dyadic_tower_synchronous_information_gap_improvement_statement m := by
  dsimp [xi_fold_zero_dyadic_tower_synchronous_information_gap_improvement_statement]
  let M : ℝ := Nat.fib (m + 3)
  let Xi : ℝ := xi_fold_zero_dyadic_tower_synchronous_information_gap_improvement_Xi m
  have hMpos : 0 < M := by
    dsimp [M]
    exact xi_fold_zero_dyadic_tower_synchronous_information_gap_improvement_main_pos m
  have hXi_nonneg : 0 ≤ Xi := by
    dsimp [Xi]
    positivity
  have hgap_pos : 0 < M - Xi := by
    dsimp [M, Xi]
    exact xi_fold_zero_dyadic_tower_synchronous_information_gap_improvement_gap_pos m
  have hcollision :
      Omega.Conclusion.zeroPacketCollisionUpperBound M Xi ≤
        Omega.Conclusion.zeroPacketCollisionUpperBound M 0 := by
    unfold Omega.Conclusion.zeroPacketCollisionUpperBound
    refine div_le_div_of_nonneg_right ?_ hMpos.le
    linarith
  have hmaxfiber :
      Omega.Conclusion.zeroPacketMaxfiberUpperBound m M Xi ≤
        Omega.Conclusion.zeroPacketMaxfiberUpperBound m M 0 := by
    unfold Omega.Conclusion.zeroPacketMaxfiberUpperBound
    have hsqrt :
        Real.sqrt (Omega.Conclusion.zeroPacketCollisionUpperBound M Xi) ≤
          Real.sqrt (Omega.Conclusion.zeroPacketCollisionUpperBound M 0) :=
      Real.sqrt_le_sqrt hcollision
    exact mul_le_mul_of_nonneg_left hsqrt (pow_nonneg (by positivity) _)
  have hentropy :
      Omega.Conclusion.zeroPacketEntropyGapUpperBound M Xi ≤
        Omega.Conclusion.zeroPacketEntropyGapUpperBound M 0 := by
    unfold Omega.Conclusion.zeroPacketEntropyGapUpperBound
    have hle : M - Xi ≤ M := by
      linarith
    simpa using Real.log_le_log hgap_pos hle
  have hfourier :
      Omega.Conclusion.zeroPacketFourierUpperBound m M Xi ≤
        Omega.Conclusion.zeroPacketFourierUpperBound m M 0 := by
    unfold Omega.Conclusion.zeroPacketFourierUpperBound
    have hsqrt : Real.sqrt (M - 1 - Xi) ≤ Real.sqrt (M - 1 - 0) := by
      apply Real.sqrt_le_sqrt
      linarith
    exact mul_le_mul_of_nonneg_left hsqrt (pow_nonneg (by positivity) _)
  refine ⟨hcollision, hmaxfiber, hentropy, hfourier, ?_⟩
  intro hm
  subst hm
  constructor
  · native_decide
  · native_decide

end Omega.Zeta
