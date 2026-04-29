import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- Concrete sliding recurrence code for the monic polynomial `P(λ) = λ^d`: every audited
window forces its trailing coordinate to vanish. -/
def pom_recurrence_code_violation_distance_isCode (d n : ℕ) (x : Fin n → ℤ) : Prop :=
  ∀ i : Fin n, d ≤ i.1 → x i = 0

/-- Count of audited windows whose trailing coordinate violates the `λ^d` recurrence. -/
def pom_recurrence_code_violation_distance_violationCount (d n : ℕ) (x : Fin n → ℤ) : ℕ :=
  (Finset.univ.filter fun i : Fin n => d ≤ i.1 ∧ x i ≠ 0).card

/-- Hamming distance on length-`n` words. -/
def pom_recurrence_code_violation_distance_hammingDist (x y : Fin n → ℤ) : ℕ :=
  (Finset.univ.filter fun i : Fin n => x i ≠ y i).card

/-- Left-to-right repair for the concrete `λ^d` recurrence: kill every offending trailing symbol. -/
def pom_recurrence_code_violation_distance_repair (d n : ℕ) (x : Fin n → ℤ) : Fin n → ℤ :=
  fun i => if _ : d ≤ i.1 then 0 else x i

/-- Paper label: `prop:pom-recurrence-code-violation-distance`. For the concrete monic recurrence
`x_{k+d} = 0`, the greedy repair changes exactly the violating trailing coordinates, and every
codeword must differ from the input on each such coordinate. This yields the advertised
violation-count/Hamming-distance sandwich. -/
theorem paper_pom_recurrence_code_violation_distance
    (d n : ℕ) (x : Fin n → ℤ) :
    ∃ c : Fin n → ℤ,
      pom_recurrence_code_violation_distance_isCode d n c ∧
      pom_recurrence_code_violation_distance_hammingDist x c =
        pom_recurrence_code_violation_distance_violationCount d n x ∧
      ∀ c' : Fin n → ℤ,
        pom_recurrence_code_violation_distance_isCode d n c' →
          pom_recurrence_code_violation_distance_violationCount d n x ≤
            (d + 1) * pom_recurrence_code_violation_distance_hammingDist x c' := by
  refine ⟨pom_recurrence_code_violation_distance_repair d n x, ?_, ?_, ?_⟩
  · intro i hi
    simp [pom_recurrence_code_violation_distance_repair, hi]
  · unfold pom_recurrence_code_violation_distance_hammingDist
      pom_recurrence_code_violation_distance_violationCount
    have hfilter :
        (Finset.univ.filter
            (fun i : Fin n =>
              x i ≠ pom_recurrence_code_violation_distance_repair d n x i)) =
          Finset.univ.filter (fun i : Fin n => d ≤ i.1 ∧ x i ≠ 0) := by
      ext i
      by_cases hi : d ≤ i.1
      · simp [pom_recurrence_code_violation_distance_repair, hi]
      · simp [pom_recurrence_code_violation_distance_repair, hi]
    rw [hfilter]
  · intro c' hc'
    have hsubset :
        Finset.univ.filter (fun i : Fin n => d ≤ i.1 ∧ x i ≠ 0) ⊆
          Finset.univ.filter
            (fun i : Fin n => x i ≠ c' i) := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      rcases hi with ⟨hdi, hxi⟩
      have hci : c' i = 0 := hc' i hdi
      simpa [hci] using hxi
    have hbase :
        pom_recurrence_code_violation_distance_violationCount d n x ≤
          pom_recurrence_code_violation_distance_hammingDist x c' := by
      unfold pom_recurrence_code_violation_distance_violationCount
        pom_recurrence_code_violation_distance_hammingDist
      exact Finset.card_le_card hsubset
    have hmul :
        pom_recurrence_code_violation_distance_hammingDist x c' ≤
          (d + 1) * pom_recurrence_code_violation_distance_hammingDist x c' := by
      simpa using
        Nat.mul_le_mul_right
          (pom_recurrence_code_violation_distance_hammingDist x c')
          (Nat.succ_le_succ (Nat.zero_le d))
    exact le_trans hbase hmul

end Omega.POM
