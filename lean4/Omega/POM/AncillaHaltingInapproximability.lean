import Mathlib.Data.Nat.Log
import Mathlib.Tactic

namespace Omega.POM

/-- The ancilla cost is the binary auxiliary-bit count `⌈log₂ b⌉`. -/
def pom_ancilla_halting_inapproximability_ancilla_bits (b : ℕ) : ℕ :=
  Nat.clog 2 b

lemma pom_ancilla_halting_inapproximability_budget_one_bits :
    pom_ancilla_halting_inapproximability_ancilla_bits 1 = 0 := by
  native_decide

lemma pom_ancilla_halting_inapproximability_budget_two_bits :
    pom_ancilla_halting_inapproximability_ancilla_bits 2 = 1 := by
  native_decide

lemma pom_ancilla_halting_inapproximability_additive_lt_one_eq
    {a b ε : ℕ} (hε : ε < 1) (ha : a ≤ b + ε) (hb : b ≤ a + ε) : a = b := by
  have hε0 : ε = 0 := by omega
  omega

/-- Paper label: `cor:pom-ancilla-halting-inapproximability`.
For a two-valued hard family whose minimal external budget is exactly `1` on halting instances and
exactly `2` on non-halting instances, the ancilla count `⌈log₂ b⌉` takes only the values `0` and
`1`. Deciding the ancilla count therefore decides halting. An additive error `< 1` or a
multiplicative factor `< 2` on this `{0,1}`-valued family collapses to exact recovery by case
separation, so such approximations are impossible under the same undecidability hypothesis. -/
theorem paper_pom_ancilla_halting_inapproximability
    {Code : Type*} (halts : Code → Prop) (minimalBudget : Code → ℕ)
    (hHaltingBudget : ∀ c : Code, halts c ↔ minimalBudget c = 1)
    (hNonhaltingBudget : ∀ c : Code, ¬ halts c ↔ minimalBudget c = 2)
    (hUndecidable : ¬ Nonempty (∀ c : Code, Decidable (halts c))) :
    (∀ c : Code,
        pom_ancilla_halting_inapproximability_ancilla_bits (minimalBudget c) = 0 ∨
          pom_ancilla_halting_inapproximability_ancilla_bits (minimalBudget c) = 1) ∧
      ¬ Nonempty
        (∀ c : Code,
          Decidable
            (pom_ancilla_halting_inapproximability_ancilla_bits (minimalBudget c) = 0)) ∧
      (∀ ε : ℕ, ε < 1 →
        ¬ ∃ A : Code → ℕ,
          ∀ c : Code,
            A c ≤
                pom_ancilla_halting_inapproximability_ancilla_bits (minimalBudget c) + ε ∧
              pom_ancilla_halting_inapproximability_ancilla_bits (minimalBudget c) ≤ A c + ε) ∧
      (∀ lam : ℝ, 1 ≤ lam → lam < 2 →
        ¬ ∃ A : Code → ℕ,
          ∀ c : Code,
            (pom_ancilla_halting_inapproximability_ancilla_bits (minimalBudget c) : ℝ) ≤ A c ∧
              (A c : ℝ) ≤
                lam *
                  pom_ancilla_halting_inapproximability_ancilla_bits (minimalBudget c)) := by
  have hBitsZeroIffHalts :
      ∀ c : Code,
        pom_ancilla_halting_inapproximability_ancilla_bits (minimalBudget c) = 0 ↔ halts c := by
    intro c
    constructor
    · intro hbits
      by_cases hc : halts c
      · exact hc
      · rw [(hNonhaltingBudget c).mp hc,
          pom_ancilla_halting_inapproximability_budget_two_bits] at hbits
        cases hbits
    · intro hc
      rw [(hHaltingBudget c).mp hc]
      exact pom_ancilla_halting_inapproximability_budget_one_bits
  have hBitsZeroOrOne :
      ∀ c : Code,
        pom_ancilla_halting_inapproximability_ancilla_bits (minimalBudget c) = 0 ∨
          pom_ancilla_halting_inapproximability_ancilla_bits (minimalBudget c) = 1 := by
    intro c
    by_cases hc : halts c
    · left
      rw [(hHaltingBudget c).mp hc]
      exact pom_ancilla_halting_inapproximability_budget_one_bits
    · right
      rw [(hNonhaltingBudget c).mp hc]
      exact pom_ancilla_halting_inapproximability_budget_two_bits
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c
    exact hBitsZeroOrOne c
  · intro hAncillaDecidable
    apply hUndecidable
    refine ⟨?_⟩
    intro c
    let hDec :
        Decidable
          (pom_ancilla_halting_inapproximability_ancilla_bits (minimalBudget c) = 0) :=
      Classical.choice hAncillaDecidable c
    exact decidable_of_iff
      (pom_ancilla_halting_inapproximability_ancilla_bits (minimalBudget c) = 0)
      (hBitsZeroIffHalts c)
  · intro ε hε hA
    rcases hA with ⟨A, hA⟩
    apply hUndecidable
    refine ⟨?_⟩
    intro c
    have hEq :
        A c =
          pom_ancilla_halting_inapproximability_ancilla_bits (minimalBudget c) := by
      exact pom_ancilla_halting_inapproximability_additive_lt_one_eq hε (hA c).1 (hA c).2
    exact decidable_of_iff (A c = 0) (by
      rw [hEq]
      exact hBitsZeroIffHalts c)
  · intro lam hlam1 hlam2 hA
    rcases hA with ⟨A, hA⟩
    apply hUndecidable
    refine ⟨?_⟩
    intro c
    have hEq :
        A c =
          pom_ancilla_halting_inapproximability_ancilla_bits (minimalBudget c) := by
      by_cases hzero :
          pom_ancilla_halting_inapproximability_ancilla_bits (minimalBudget c) = 0
      · have hupper := (hA c).2
        rw [hzero] at hupper
        have hupper0 : (A c : ℝ) ≤ 0 := by simpa using hupper
        have hAeq0 : (A c : ℝ) = 0 := le_antisymm hupper0 (by positivity)
        exact Nat.cast_eq_zero.mp hAeq0 ▸ hzero.symm
      · have hone :
            pom_ancilla_halting_inapproximability_ancilla_bits (minimalBudget c) = 1 := by
          rcases hBitsZeroOrOne c with h0 | h1
          · exact False.elim (hzero h0)
          · exact h1
        have hlower_nat : 1 ≤ A c := by
          have hlower := (hA c).1
          rw [hone] at hlower
          exact_mod_cast hlower
        have hupper_lt_two : (A c : ℝ) < 2 := by
          have hupper := (hA c).2
          rw [hone] at hupper
          have hupper' : (A c : ℝ) ≤ lam := by simpa using hupper
          exact lt_of_le_of_lt hupper' hlam2
        have hupper_nat : A c < 2 := by
          exact_mod_cast hupper_lt_two
        omega
    exact decidable_of_iff (A c = 0) (by
      rw [hEq]
      exact hBitsZeroIffHalts c)

end Omega.POM
