import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Data.Finset.Interval
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Omega.Conclusion.F2BinomialBasisFromDeltaNilpotent

namespace Omega.POM

open scoped fwdDiff

/-- Audited `a_q` exponents for `q = 4, …, 11`. -/
def pom_charpoly_mod2_closed_exponent_law_q4_11_audited_a : ℕ → ℕ
  | 4 => 3
  | 5 => 3
  | 6 => 5
  | 7 => 3
  | 8 => 5
  | 9 => 3
  | 10 => 5
  | 11 => 3
  | _ => 0

/-- Audited `b_q` exponents for `q = 4, …, 11`. -/
def pom_charpoly_mod2_closed_exponent_law_q4_11_audited_b : ℕ → ℕ
  | 4 => 2
  | 5 => 2
  | 6 => 2
  | 7 => 4
  | 8 => 4
  | 9 => 4
  | 10 => 4
  | 11 => 6
  | _ => 0

/-- Closed formula for `a_q` on the audited range. -/
def pom_charpoly_mod2_closed_exponent_law_q4_11_closed_a (q : ℕ) : ℕ :=
  3 + 2 * if q % 2 = 0 ∧ 6 ≤ q then 1 else 0

/-- Closed formula for `b_q` on the audited range. -/
def pom_charpoly_mod2_closed_exponent_law_q4_11_closed_b (q : ℕ) : ℕ :=
  2 * ((q + 1) / 4)

/-- The forward-shift annihilation operator `E^{a_q}(E + 1)^{b_q}` written as an iterated forward
difference on the shifted sequence. -/
def pom_charpoly_mod2_closed_exponent_law_q4_11_annihilation_operator
    (q : ℕ) (S : ℕ → ZMod 2) : ℕ → ZMod 2 :=
  Nat.iterate Omega.Conclusion.forwardDiff (pom_charpoly_mod2_closed_exponent_law_q4_11_audited_b q)
    (fun m => S (m + pom_charpoly_mod2_closed_exponent_law_q4_11_audited_a q))

/-- The audited exponents agree with the closed formulas on `4 ≤ q ≤ 11`, and the associated
forward-shift annihilation operator is exactly `E^{a_q}(E + 1)^{b_q}` on that range. -/
def pom_charpoly_mod2_closed_exponent_law_q4_11_statement : Prop :=
  (∀ q ∈ Finset.Icc 4 11,
      pom_charpoly_mod2_closed_exponent_law_q4_11_audited_a q =
        pom_charpoly_mod2_closed_exponent_law_q4_11_closed_a q ∧
      pom_charpoly_mod2_closed_exponent_law_q4_11_audited_b q =
        pom_charpoly_mod2_closed_exponent_law_q4_11_closed_b q) ∧
    (∀ q ∈ Finset.Icc 4 11, ∀ S : ℕ → ZMod 2,
      pom_charpoly_mod2_closed_exponent_law_q4_11_annihilation_operator q S =
        Nat.iterate Omega.Conclusion.forwardDiff
          (pom_charpoly_mod2_closed_exponent_law_q4_11_closed_b q)
          (fun m => S (m + pom_charpoly_mod2_closed_exponent_law_q4_11_closed_a q)))

theorem paper_pom_charpoly_mod2_closed_exponent_law_q4_11 :
    pom_charpoly_mod2_closed_exponent_law_q4_11_statement := by
  constructor
  · intro q hq
    rw [Finset.mem_Icc] at hq
    have hcases : q = 4 ∨ q = 5 ∨ q = 6 ∨ q = 7 ∨ q = 8 ∨ q = 9 ∨ q = 10 ∨ q = 11 := by
      omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> native_decide
  · intro q hq S
    rw [Finset.mem_Icc] at hq
    have hcases : q = 4 ∨ q = 5 ∨ q = 6 ∨ q = 7 ∨ q = 8 ∨ q = 9 ∨ q = 10 ∨ q = 11 := by
      omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [pom_charpoly_mod2_closed_exponent_law_q4_11_annihilation_operator,
        pom_charpoly_mod2_closed_exponent_law_q4_11_audited_a,
        pom_charpoly_mod2_closed_exponent_law_q4_11_audited_b,
        pom_charpoly_mod2_closed_exponent_law_q4_11_closed_a,
        pom_charpoly_mod2_closed_exponent_law_q4_11_closed_b]

end Omega.POM
