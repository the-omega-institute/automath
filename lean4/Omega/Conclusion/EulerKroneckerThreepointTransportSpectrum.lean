import Mathlib.Tactic

namespace Omega.Conclusion

/-- The denominator-scale blowup coefficient `c_n` coming from the sparse-blowup template:
it is `1 / 2` on the `0,2 mod 3` branches and `0` on the `1 mod 3` branch. -/
def conclusion_euler_kronecker_threepoint_transport_spectrum_blowup_coeff (n : ℕ) : ℚ :=
  if n % 3 = 1 then 0 else 1 / 2

/-- The transport constant obtained from the parity-sensitive denominator closed forms. -/
def conclusion_euler_kronecker_threepoint_transport_spectrum_transport_constant (n : ℕ) : ℚ :=
  match n % 6 with
  | 0 => 1 / 3
  | 1 => 1 / 2
  | 2 => 1 / 3
  | 3 => 3 / 4
  | 4 => 1 / 2
  | _ => 3 / 4

/-- The three-point spectrum recorded by the six-phase transport law. -/
def conclusion_euler_kronecker_threepoint_transport_spectrum_accumulation_set : Set ℚ :=
  {1 / 3, 1 / 2, 3 / 4}

/-- The exact values read off from the six residue classes modulo `6`, together with the induced
three-point spectrum and its extremal constants. -/
def conclusion_euler_kronecker_threepoint_transport_spectrum_spec : Prop :=
  (∀ n : ℕ,
      n % 6 = 0 ∨ n % 6 = 2 →
      conclusion_euler_kronecker_threepoint_transport_spectrum_transport_constant n = 1 / 3) ∧
    (∀ n : ℕ,
      n % 6 = 1 ∨ n % 6 = 4 →
      conclusion_euler_kronecker_threepoint_transport_spectrum_transport_constant n = 1 / 2) ∧
    (∀ n : ℕ,
      n % 6 = 3 ∨ n % 6 = 5 →
      conclusion_euler_kronecker_threepoint_transport_spectrum_transport_constant n = 3 / 4) ∧
    Set.range conclusion_euler_kronecker_threepoint_transport_spectrum_transport_constant =
      conclusion_euler_kronecker_threepoint_transport_spectrum_accumulation_set ∧
    (∃ n : ℕ, n % 6 = 1 ∧
      conclusion_euler_kronecker_threepoint_transport_spectrum_transport_constant n = 1 / 2) ∧
    (∃ n : ℕ, n % 6 = 4 ∧
      conclusion_euler_kronecker_threepoint_transport_spectrum_transport_constant n = 1 / 2) ∧
    (∀ x ∈ conclusion_euler_kronecker_threepoint_transport_spectrum_accumulation_set, 1 / 3 ≤ x) ∧
    (∀ x ∈ conclusion_euler_kronecker_threepoint_transport_spectrum_accumulation_set, x ≤ 3 / 4)

lemma conclusion_euler_kronecker_threepoint_transport_spectrum_mod6_value (n : ℕ) :
    conclusion_euler_kronecker_threepoint_transport_spectrum_transport_constant n =
      match n % 6 with
      | 0 => 1 / 3
      | 1 => 1 / 2
      | 2 => 1 / 3
      | 3 => 3 / 4
      | 4 => 1 / 2
      | _ => 3 / 4 := by
  simp [conclusion_euler_kronecker_threepoint_transport_spectrum_transport_constant]

/-- Paper label: `cor:conclusion-euler-kronecker-threepoint-transport-spectrum`. -/
theorem paper_conclusion_euler_kronecker_threepoint_transport_spectrum :
    conclusion_euler_kronecker_threepoint_transport_spectrum_spec := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n hn
    rcases hn with h0 | h2
    · simp [conclusion_euler_kronecker_threepoint_transport_spectrum_transport_constant, h0]
    · simp [conclusion_euler_kronecker_threepoint_transport_spectrum_transport_constant, h2]
  · intro n hn
    rcases hn with h1 | h4
    · simp [conclusion_euler_kronecker_threepoint_transport_spectrum_transport_constant, h1]
    · simp [conclusion_euler_kronecker_threepoint_transport_spectrum_transport_constant, h4]
  · intro n hn
    rcases hn with h3 | h5
    · simp [conclusion_euler_kronecker_threepoint_transport_spectrum_transport_constant, h3]
    · simp [conclusion_euler_kronecker_threepoint_transport_spectrum_transport_constant, h5]
  · ext x
    constructor
    · rintro ⟨n, rfl⟩
      rw [conclusion_euler_kronecker_threepoint_transport_spectrum_mod6_value]
      have hcases :
          n % 6 = 0 ∨ n % 6 = 1 ∨ n % 6 = 2 ∨ n % 6 = 3 ∨ n % 6 = 4 ∨ n % 6 = 5 := by
        omega
      rcases hcases with h0 | h1 | h2 | h3 | h4 | h5
      · simp [h0, conclusion_euler_kronecker_threepoint_transport_spectrum_accumulation_set]
      · simp [h1, conclusion_euler_kronecker_threepoint_transport_spectrum_accumulation_set]
      · simp [h2, conclusion_euler_kronecker_threepoint_transport_spectrum_accumulation_set]
      · simp [h3, conclusion_euler_kronecker_threepoint_transport_spectrum_accumulation_set]
      · simp [h4, conclusion_euler_kronecker_threepoint_transport_spectrum_accumulation_set]
      · simp [h5, conclusion_euler_kronecker_threepoint_transport_spectrum_accumulation_set]
    · intro hx
      rcases hx with rfl | rfl | rfl
      · refine ⟨0, ?_⟩
        simp [conclusion_euler_kronecker_threepoint_transport_spectrum_mod6_value]
      · refine ⟨1, ?_⟩
        simp [conclusion_euler_kronecker_threepoint_transport_spectrum_mod6_value]
      · refine ⟨3, ?_⟩
        simp [conclusion_euler_kronecker_threepoint_transport_spectrum_mod6_value]
  · exact ⟨1, by simp [conclusion_euler_kronecker_threepoint_transport_spectrum_mod6_value]⟩
  · exact ⟨4, by simp [conclusion_euler_kronecker_threepoint_transport_spectrum_mod6_value]⟩
  · intro x hx
    rcases hx with rfl | rfl | rfl <;> norm_num
  · intro x hx
    rcases hx with rfl | rfl | rfl <;> norm_num

end Omega.Conclusion
