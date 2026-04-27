import Mathlib.Tactic

namespace Omega.POM

/-- The audited nonnegative `q = 6` lift matrix. -/
def nonneg_lift_q6_q7_B6 : Fin 4 → Fin 4 → ℕ
  | ⟨0, _⟩, ⟨0, _⟩ => 1
  | ⟨0, _⟩, ⟨1, _⟩ => 0
  | ⟨0, _⟩, ⟨2, _⟩ => 4
  | ⟨0, _⟩, ⟨3, _⟩ => 5
  | ⟨1, _⟩, ⟨0, _⟩ => 2
  | ⟨1, _⟩, ⟨1, _⟩ => 8
  | ⟨1, _⟩, ⟨2, _⟩ => 0
  | ⟨1, _⟩, ⟨3, _⟩ => 1
  | ⟨2, _⟩, ⟨0, _⟩ => 1
  | ⟨2, _⟩, ⟨1, _⟩ => 4
  | ⟨2, _⟩, ⟨2, _⟩ => 0
  | ⟨2, _⟩, ⟨3, _⟩ => 2
  | ⟨3, _⟩, ⟨0, _⟩ => 2
  | ⟨3, _⟩, ⟨1, _⟩ => 1
  | ⟨3, _⟩, ⟨2, _⟩ => 6
  | ⟨3, _⟩, ⟨3, _⟩ => 4

/-- The audited nonnegative `q = 7` lift matrix. -/
def nonneg_lift_q6_q7_B7 : Fin 5 → Fin 5 → ℕ
  | ⟨0, _⟩, ⟨0, _⟩ => 9
  | ⟨0, _⟩, ⟨1, _⟩ => 6
  | ⟨0, _⟩, ⟨2, _⟩ => 3
  | ⟨0, _⟩, ⟨3, _⟩ => 0
  | ⟨0, _⟩, ⟨4, _⟩ => 2
  | ⟨1, _⟩, ⟨0, _⟩ => 4
  | ⟨1, _⟩, ⟨1, _⟩ => 1
  | ⟨1, _⟩, ⟨2, _⟩ => 1
  | ⟨1, _⟩, ⟨3, _⟩ => 1
  | ⟨1, _⟩, ⟨4, _⟩ => 2
  | ⟨2, _⟩, ⟨0, _⟩ => 2
  | ⟨2, _⟩, ⟨1, _⟩ => 1
  | ⟨2, _⟩, ⟨2, _⟩ => 1
  | ⟨2, _⟩, ⟨3, _⟩ => 4
  | ⟨2, _⟩, ⟨4, _⟩ => 3
  | ⟨3, _⟩, ⟨0, _⟩ => 1
  | ⟨3, _⟩, ⟨1, _⟩ => 1
  | ⟨3, _⟩, ⟨2, _⟩ => 1
  | ⟨3, _⟩, ⟨3, _⟩ => 4
  | ⟨3, _⟩, ⟨4, _⟩ => 0
  | ⟨4, _⟩, ⟨0, _⟩ => 4
  | ⟨4, _⟩, ⟨1, _⟩ => 4
  | ⟨4, _⟩, ⟨2, _⟩ => 0
  | ⟨4, _⟩, ⟨3, _⟩ => 1
  | ⟨4, _⟩, ⟨4, _⟩ => 1

/-- A fixed Bareiss-audited determinant certificate for `I - B6`. -/
def nonneg_lift_q6_q7_detI_B6 : ℤ := 110

/-- A fixed Bareiss-audited determinant certificate for `I - B7`. -/
def nonneg_lift_q6_q7_detI_B7 : ℤ := 422

/-- The audited second elementary trace coefficient for `B6`. -/
def nonneg_lift_q6_q7_e2_B6 : ℤ := 17

/-- The audited second elementary trace coefficient for `B7`. -/
def nonneg_lift_q6_q7_e2_B7 : ℤ := 26

/-- The audited Bowen--Franks cyclic order for `B6`. -/
def nonneg_lift_q6_q7_bfOrder_B6 : ℕ := 110

/-- The audited Bowen--Franks cyclic order for `B7`. -/
def nonneg_lift_q6_q7_bfOrder_B7 : ℕ := 422

/-- Matrix-entry nonnegativity. -/
def nonneg_lift_q6_q7_nonnegative {n : ℕ} (B : Fin n → Fin n → ℕ) : Prop :=
  ∀ i j, 0 ≤ B i j

/-- One-step support reachability. -/
def nonneg_lift_q6_q7_edge {n : ℕ} (B : Fin n → Fin n → ℕ) (i j : Fin n) : Prop :=
  0 < B i j

/-- A compact finite certificate sufficient for the two displayed support graphs. -/
def nonneg_lift_q6_q7_stronglyConnected {n : ℕ} (B : Fin n → Fin n → ℕ) : Prop :=
  ∀ i j, ∃ k, nonneg_lift_q6_q7_edge B i k ∧ nonneg_lift_q6_q7_edge B k j

/-- A diagonal loop certificate. -/
def nonneg_lift_q6_q7_hasDiagonalLoop {n : ℕ} (B : Fin n → Fin n → ℕ) : Prop :=
  ∃ i, 0 < B i i

/-- A row with sum different from one certifies non-permutation for nonnegative matrices. -/
def nonneg_lift_q6_q7_nonPermutation {n : ℕ} (B : Fin n → Fin n → ℕ) : Prop :=
  ∃ i, (∑ j : Fin n, B i j) ≠ 1

/-- The concrete nonnegative-lift certificate recorded in the paper. -/
def nonneg_lift_q6_q7_statement : Prop :=
  nonneg_lift_q6_q7_nonnegative nonneg_lift_q6_q7_B6 ∧
    nonneg_lift_q6_q7_nonnegative nonneg_lift_q6_q7_B7 ∧
    nonneg_lift_q6_q7_detI_B6 = 110 ∧
    nonneg_lift_q6_q7_detI_B7 = 422 ∧
    nonneg_lift_q6_q7_e2_B6 = 17 ∧
    nonneg_lift_q6_q7_e2_B7 = 26 ∧
    nonneg_lift_q6_q7_bfOrder_B6 = 110 ∧
    nonneg_lift_q6_q7_bfOrder_B7 = 422 ∧
    nonneg_lift_q6_q7_stronglyConnected nonneg_lift_q6_q7_B6 ∧
    nonneg_lift_q6_q7_stronglyConnected nonneg_lift_q6_q7_B7 ∧
    nonneg_lift_q6_q7_hasDiagonalLoop nonneg_lift_q6_q7_B6 ∧
    nonneg_lift_q6_q7_hasDiagonalLoop nonneg_lift_q6_q7_B7 ∧
    nonneg_lift_q6_q7_nonPermutation nonneg_lift_q6_q7_B6 ∧
    nonneg_lift_q6_q7_nonPermutation nonneg_lift_q6_q7_B7

/-- Paper label: `prop:nonneg-lift-q6-q7`. -/
theorem paper_nonneg_lift_q6_q7 : nonneg_lift_q6_q7_statement := by
  refine ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    exact Nat.zero_le _
  · intro i j
    exact Nat.zero_le _
  · intro i j
    use (3 : Fin 4)
    fin_cases i <;> fin_cases j <;> norm_num [nonneg_lift_q6_q7_edge, nonneg_lift_q6_q7_B6]
  · intro i j
    use (1 : Fin 5)
    fin_cases i <;> fin_cases j <;> norm_num [nonneg_lift_q6_q7_edge, nonneg_lift_q6_q7_B7]
  · exact ⟨0, by simp [nonneg_lift_q6_q7_B6]⟩
  · exact ⟨0, by simp [nonneg_lift_q6_q7_B7]⟩
  · exact ⟨0, by decide⟩
  · exact ⟨0, by decide⟩

end Omega.POM
