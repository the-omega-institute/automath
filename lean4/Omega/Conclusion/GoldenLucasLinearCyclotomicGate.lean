import Mathlib.Data.Int.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- The midpoint root appearing in the golden specialization of the Lucas Hankel gate. -/
def conclusion_golden_lucas_linear_cyclotomic_gate_midpoint_root (q : ℕ) : ℤ :=
  (-1 : ℤ) ^ (q / 2)

/-- Paper-facing packaging of the three `q mod 4` branches for the midpoint root in the golden
specialization: `q ≡ 0 mod 4` gives the root `1`, `q ≡ 2 mod 4` gives the root `-1`, and odd `q`
admit no midpoint index. -/
def conclusion_golden_lucas_linear_cyclotomic_gate_statement : Prop :=
  (∀ q : ℕ, q % 4 = 0 →
    Even q ∧ conclusion_golden_lucas_linear_cyclotomic_gate_midpoint_root q = 1) ∧
  (∀ q : ℕ, q % 4 = 2 →
    Even q ∧ conclusion_golden_lucas_linear_cyclotomic_gate_midpoint_root q = -1) ∧
  (∀ q : ℕ, q % 2 = 1 → ¬ ∃ k : ℕ, 2 * k = q)

theorem paper_conclusion_golden_lucas_linear_cyclotomic_gate :
    conclusion_golden_lucas_linear_cyclotomic_gate_statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    let n := q / 4
    have hq' : q = 4 * n := by
      have h := Nat.mod_add_div q 4
      rw [hq, zero_add] at h
      simpa [n, Nat.mul_comm] using h.symm
    have heven : Even q := ⟨2 * n, by omega⟩
    have hhalf : q / 2 = 2 * n := by
      rw [hq']
      have hfour : 4 * n = (2 * n) * 2 := by omega
      rw [hfour]
      simp
    refine ⟨heven, ?_⟩
    simp [conclusion_golden_lucas_linear_cyclotomic_gate_midpoint_root, hhalf]
  · intro q hq
    let n := q / 4
    have hq' : q = 4 * n + 2 := by
      have h := Nat.mod_add_div q 4
      rw [hq] at h
      simpa [n, Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h.symm
    have heven : Even q := ⟨2 * n + 1, by omega⟩
    have hhalf : q / 2 = 2 * n + 1 := by
      rw [hq']
      have hfour : 4 * n = (2 * n) * 2 := by omega
      rw [hfour]
      simp
    refine ⟨heven, ?_⟩
    simp [conclusion_golden_lucas_linear_cyclotomic_gate_midpoint_root, hhalf, pow_add, pow_mul]
  · intro q hq hmid
    rcases hmid with ⟨k, hk⟩
    omega

end Omega.Conclusion
