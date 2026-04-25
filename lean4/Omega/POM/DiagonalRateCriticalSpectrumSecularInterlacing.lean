import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

/-- Concrete critical-spectrum witness: in every positive probability vector with at least two
coordinates summing to `1`, there are two distinct diagonal poles strictly to the right of the
critical point `1`. -/
def pom_diagonal_rate_critical_spectrum_secular_interlacing_statement
    (k : ℕ) (q : Fin k → ℚ) : Prop :=
  ∃ i j : Fin k, i ≠ j ∧ (1 : ℚ) < 1 / q i ∧ (1 : ℚ) < 1 / q j

/-- Paper label: `thm:pom-diagonal-rate-critical-spectrum-secular-interlacing`. -/
theorem paper_pom_diagonal_rate_critical_spectrum_secular_interlacing
    (k : ℕ) (hk : 2 ≤ k) (q : Fin k → ℚ) (hq_pos : ∀ i, 0 < q i)
    (hq_sum : (∑ i, q i) = 1) :
    pom_diagonal_rate_critical_spectrum_secular_interlacing_statement k q := by
  let i0 : Fin k := ⟨0, by omega⟩
  let i1 : Fin k := ⟨1, by omega⟩
  have hi01 : i0 ≠ i1 := by
    intro h
    have hvals : (0 : ℕ) = 1 := by simpa [i0, i1] using congrArg Fin.val h
    omega
  have hi1_mem : i1 ∈ (Finset.univ : Finset (Fin k)).erase i0 := by
    simp [i0, i1, hi01]
  have hi0_mem : i0 ∈ (Finset.univ : Finset (Fin k)).erase i1 := by
    simp [i0, i1, hi01]
  have hrest0_pos :
      0 < Finset.sum ((Finset.univ : Finset (Fin k)).erase i0) (fun i => q i) := by
    have hle :
        q i1 ≤ Finset.sum ((Finset.univ : Finset (Fin k)).erase i0) (fun i => q i) := by
      exact Finset.single_le_sum (fun i _ => le_of_lt (hq_pos i)) hi1_mem
    exact lt_of_lt_of_le (hq_pos i1) hle
  have hrest1_pos :
      0 < Finset.sum ((Finset.univ : Finset (Fin k)).erase i1) (fun i => q i) := by
    have hle :
        q i0 ≤ Finset.sum ((Finset.univ : Finset (Fin k)).erase i1) (fun i => q i) := by
      exact Finset.single_le_sum (fun i _ => le_of_lt (hq_pos i)) hi0_mem
    exact lt_of_lt_of_le (hq_pos i0) hle
  have hsum0 :
      q i0 + Finset.sum ((Finset.univ : Finset (Fin k)).erase i0) (fun i => q i) = ∑ i, q i := by
    simpa [add_comm] using
      (Finset.sum_erase_add (s := (Finset.univ : Finset (Fin k))) (a := i0)
        (f := fun i => q i) (by simp))
  have hsum1 :
      q i1 + Finset.sum ((Finset.univ : Finset (Fin k)).erase i1) (fun i => q i) = ∑ i, q i := by
    simpa [add_comm] using
      (Finset.sum_erase_add (s := (Finset.univ : Finset (Fin k))) (a := i1)
        (f := fun i => q i) (by simp))
  have hq0_lt_one : q i0 < 1 := by
    have hlt : q i0 < ∑ i, q i := by
      linarith
    simpa [hq_sum] using hlt
  have hq1_lt_one : q i1 < 1 := by
    have hlt : q i1 < ∑ i, q i := by
      linarith
    simpa [hq_sum] using hlt
  have hq0_inv : (1 : ℚ) < 1 / q i0 := by
    by_contra h
    have hle : 1 / q i0 ≤ 1 := le_of_not_gt h
    have hmul := mul_le_mul_of_nonneg_left hle (le_of_lt (hq_pos i0))
    have hq0_ne : q i0 ≠ 0 := by linarith [hq_pos i0]
    have hone : (1 : ℚ) ≤ q i0 := by
      simpa [div_eq_mul_inv, hq0_ne, mul_comm, mul_left_comm, mul_assoc] using hmul
    linarith
  have hq1_inv : (1 : ℚ) < 1 / q i1 := by
    by_contra h
    have hle : 1 / q i1 ≤ 1 := le_of_not_gt h
    have hmul := mul_le_mul_of_nonneg_left hle (le_of_lt (hq_pos i1))
    have hq1_ne : q i1 ≠ 0 := by linarith [hq_pos i1]
    have hone : (1 : ℚ) ≤ q i1 := by
      simpa [div_eq_mul_inv, hq1_ne, mul_comm, mul_left_comm, mul_assoc] using hmul
    linarith
  exact ⟨i0, i1, hi01, hq0_inv, hq1_inv⟩

end Omega.POM
