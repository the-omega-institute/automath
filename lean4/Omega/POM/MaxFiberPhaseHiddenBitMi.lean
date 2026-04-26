import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic
import Omega.POM.FoldInversionZeroRateStrongConverse

namespace Omega.POM

noncomputable section

lemma pom_max_fiber_phase_hidden_bit_mi_log2_ne_zero : Real.log 2 ≠ 0 := by
  have hlog2_pos : 0 < Real.log 2 := by
    exact Real.log_pos (by norm_num)
  linarith

lemma pom_max_fiber_phase_hidden_bit_mi_log2_half :
    log2 (1 / 2 : ℝ) = -1 := by
  unfold log2
  rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
  field_simp [pom_max_fiber_phase_hidden_bit_mi_log2_ne_zero]

lemma pom_max_fiber_phase_hidden_bit_mi_entropy_half :
    pomBinaryEntropy (1 / 2 : ℝ) = 1 := by
  unfold pomBinaryEntropy
  rw [pom_max_fiber_phase_hidden_bit_mi_log2_half, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num,
    pom_max_fiber_phase_hidden_bit_mi_log2_half]
  ring

lemma pom_max_fiber_phase_hidden_bit_mi_entropy_complement (p : ℝ) :
    pomBinaryEntropy (1 - p) = pomBinaryEntropy p := by
  unfold pomBinaryEntropy
  rw [show 1 - (1 - p) = p by ring]
  ring_nf

lemma pom_max_fiber_phase_hidden_bit_mi_even_prob_sum (k : ℕ) :
    ((Nat.fib k : ℝ) / (Nat.fib (k + 2) : ℝ)) +
        ((Nat.fib (k + 1) : ℝ) / (Nat.fib (k + 2) : ℝ)) =
      1 := by
  have hden_pos : 0 < (Nat.fib (k + 2) : ℝ) := by
    exact_mod_cast Nat.fib_pos.mpr (by omega : 0 < k + 2)
  have hden_ne : (Nat.fib (k + 2) : ℝ) ≠ 0 := hden_pos.ne'
  have hfib : (Nat.fib (k + 2) : ℝ) = Nat.fib k + Nat.fib (k + 1) := by
    exact_mod_cast Nat.fib_add_two (n := k)
  field_simp [hden_ne]
  nlinarith [hfib]

lemma pom_max_fiber_phase_hidden_bit_mi_odd_prob_sum (k : ℕ) :
    ((1 / 2 : ℝ) + (Nat.fib k : ℝ) / (2 * Nat.fib (k + 3) : ℝ)) +
        ((1 / 2 : ℝ) - (Nat.fib k : ℝ) / (2 * Nat.fib (k + 3) : ℝ)) =
      1 := by
  ring

/-- Paper label: `cor:pom-max-fiber-phase-hidden-bit-mi`. The stable even/odd phase-split formulas
show that the phase-averaged hidden bit is unbiased, so the mutual information reduces to
`1 - E[H(B | X)]`; the complementary phase pairs then collapse the conditional-entropy average to
the stated Fibonacci formulas. -/
theorem paper_pom_max_fiber_phase_hidden_bit_mi :
    (∀ k : ℕ,
      let p₀ : ℝ := (Nat.fib k : ℝ) / (Nat.fib (k + 2) : ℝ)
      let p₁ : ℝ := (Nat.fib (k + 1) : ℝ) / (Nat.fib (k + 2) : ℝ)
      pomBinaryEntropy ((p₀ + p₁) / 2) = 1 ∧
        (1 - (pomBinaryEntropy p₀ + pomBinaryEntropy p₁) / 2 =
          1 - pomBinaryEntropy p₀)) ∧
      (∀ k : ℕ,
        let δ : ℝ := (Nat.fib k : ℝ) / (2 * Nat.fib (k + 3) : ℝ)
        let pPlus : ℝ := (1 / 2 : ℝ) + δ
        let pMinus : ℝ := (1 / 2 : ℝ) - δ
        pomBinaryEntropy (((1 / 2 : ℝ) + (1 / 2 : ℝ) + pPlus + pMinus) / 4) = 1 ∧
          (1 - (pomBinaryEntropy (1 / 2 : ℝ) + pomBinaryEntropy pPlus +
                pomBinaryEntropy pMinus + pomBinaryEntropy (1 / 2 : ℝ)) / 4 =
            1 - (1 / 2 : ℝ) * (1 + pomBinaryEntropy pPlus))) := by
  constructor
  · intro k
    dsimp
    have hsum : ((Nat.fib k : ℝ) / (Nat.fib (k + 2) : ℝ)) +
          ((Nat.fib (k + 1) : ℝ) / (Nat.fib (k + 2) : ℝ)) = 1 :=
      pom_max_fiber_phase_hidden_bit_mi_even_prob_sum k
    have hcomp :
        pomBinaryEntropy ((Nat.fib (k + 1) : ℝ) / (Nat.fib (k + 2) : ℝ)) =
          pomBinaryEntropy ((Nat.fib k : ℝ) / (Nat.fib (k + 2) : ℝ)) := by
      have hp1 :
          ((Nat.fib (k + 1) : ℝ) / (Nat.fib (k + 2) : ℝ)) =
            1 - ((Nat.fib k : ℝ) / (Nat.fib (k + 2) : ℝ)) := by
        nlinarith [hsum]
      rw [hp1, pom_max_fiber_phase_hidden_bit_mi_entropy_complement]
    constructor
    · have havg :
          (((Nat.fib k : ℝ) / (Nat.fib (k + 2) : ℝ)) +
              ((Nat.fib (k + 1) : ℝ) / (Nat.fib (k + 2) : ℝ))) / 2 =
            1 / 2 := by
        nlinarith [hsum]
      rw [havg, pom_max_fiber_phase_hidden_bit_mi_entropy_half]
    · rw [hcomp]
      ring
  · intro k
    dsimp
    have hsum :
        ((1 / 2 : ℝ) + (Nat.fib k : ℝ) / (2 * Nat.fib (k + 3) : ℝ)) +
            ((1 / 2 : ℝ) - (Nat.fib k : ℝ) / (2 * Nat.fib (k + 3) : ℝ)) =
          1 := pom_max_fiber_phase_hidden_bit_mi_odd_prob_sum k
    have hcomp :
        pomBinaryEntropy
            ((1 / 2 : ℝ) - (Nat.fib k : ℝ) / (2 * Nat.fib (k + 3) : ℝ)) =
          pomBinaryEntropy
            ((1 / 2 : ℝ) + (Nat.fib k : ℝ) / (2 * Nat.fib (k + 3) : ℝ)) := by
      have hpminus :
          ((1 / 2 : ℝ) - (Nat.fib k : ℝ) / (2 * Nat.fib (k + 3) : ℝ)) =
            1 - ((1 / 2 : ℝ) + (Nat.fib k : ℝ) / (2 * Nat.fib (k + 3) : ℝ)) := by
        nlinarith [hsum]
      rw [hpminus, pom_max_fiber_phase_hidden_bit_mi_entropy_complement]
    constructor
    · have havg :
          (((1 / 2 : ℝ) + (1 / 2 : ℝ) +
                ((1 / 2 : ℝ) + (Nat.fib k : ℝ) / (2 * Nat.fib (k + 3) : ℝ)) +
                ((1 / 2 : ℝ) - (Nat.fib k : ℝ) / (2 * Nat.fib (k + 3) : ℝ))) / 4) =
            1 / 2 := by
        nlinarith [hsum]
      rw [havg, pom_max_fiber_phase_hidden_bit_mi_entropy_half]
    · rw [pom_max_fiber_phase_hidden_bit_mi_entropy_half, hcomp]
      ring

end

end Omega.POM
