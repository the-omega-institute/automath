import Mathlib.Tactic
import Omega.Zeta.XiTimePart60ab2ExactDarkModeArithmeticCriterion

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9u-minusone-darkmode-even-modulus`. -/
theorem paper_xi_time_part9u_minusone_darkmode_even_modulus
    (m M : ℕ) (zeroMode : ZMod M → Prop) (Dminus : ℂ)
    (hM : M = Nat.fib (m + 2))
    (hcrit : ∀ k : ZMod M,
      zeroMode k ↔
        Even M ∧ ∃ j : ℕ, 1 ≤ j ∧ j ≤ m ∧
          k * (Nat.fib (j + 1) : ZMod M) = ((M / 2 : ℕ) : ZMod M))
    (hD : zeroMode ((M / 2 : ℕ) : ZMod M) → Dminus = 0) :
    ((m + 2) % 3 = 0 ↔ Even M) ∧
      (((m + 2) % 3 = 0) ↔ zeroMode ((M / 2 : ℕ) : ZMod M)) ∧
      (((m + 2) % 3 = 0) → Dminus = 0) := by
  subst M
  have hdark :=
    paper_xi_time_part60ab2_exact_dark_mode_arithmetic_criterion
      m (Nat.fib (m + 2)) zeroMode rfl hcrit
  have hmod : (m + 2) % 3 = 0 ↔ m % 3 = 1 := by
    omega
  have hzero_to_even :
      zeroMode ((Nat.fib (m + 2) / 2 : ℕ) : ZMod (Nat.fib (m + 2))) →
        Even (Nat.fib (m + 2)) := by
    intro hzero
    exact ((hcrit ((Nat.fib (m + 2) / 2 : ℕ) : ZMod (Nat.fib (m + 2)))).mp hzero).1
  have hEven_iff_zero :
      Even (Nat.fib (m + 2)) ↔
        zeroMode ((Nat.fib (m + 2) / 2 : ℕ) : ZMod (Nat.fib (m + 2))) :=
    ⟨hdark.1, hzero_to_even⟩
  have hmod_iff_even : (m + 2) % 3 = 0 ↔ Even (Nat.fib (m + 2)) := by
    constructor
    · intro hm
      exact hEven_iff_zero.mpr (hdark.2.mp (hmod.mp hm))
    · intro hEven
      exact hmod.mpr (hdark.2.mpr (hEven_iff_zero.mp hEven))
  have hmod_iff_zero :
      (m + 2) % 3 = 0 ↔
        zeroMode ((Nat.fib (m + 2) / 2 : ℕ) : ZMod (Nat.fib (m + 2))) := by
    constructor
    · intro hm
      exact hdark.2.mp (hmod.mp hm)
    · intro hzero
      exact hmod.mpr (hdark.2.mpr hzero)
  exact ⟨hmod_iff_even, hmod_iff_zero, fun hm => hD (hmod_iff_zero.mp hm)⟩

end Omega.Zeta
