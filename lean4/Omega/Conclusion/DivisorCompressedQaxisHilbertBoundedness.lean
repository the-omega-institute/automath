import Mathlib

open scoped BigOperators

namespace Omega.Conclusion

structure conclusion_divisor_compressed_qaxis_hilbert_boundedness_data where
  q : ℕ
  signal : ℕ → ℝ

def conclusion_divisor_compressed_qaxis_hilbert_boundedness_axis
    (D : conclusion_divisor_compressed_qaxis_hilbert_boundedness_data) : Finset ℕ :=
  Finset.Icc 1 D.q

noncomputable def conclusion_divisor_compressed_qaxis_hilbert_boundedness_operator
    (D : conclusion_divisor_compressed_qaxis_hilbert_boundedness_data) (n : ℕ) : ℝ :=
  Finset.sum n.divisors fun d => D.signal d / (d : ℝ)

def conclusion_divisor_compressed_qaxis_hilbert_boundedness_local_energy
    (D : conclusion_divisor_compressed_qaxis_hilbert_boundedness_data) (n : ℕ) : ℝ :=
  Finset.sum n.divisors fun d => |D.signal d| ^ 2

noncomputable def conclusion_divisor_compressed_qaxis_hilbert_boundedness_divisor_weight
    (n : ℕ) : ℝ :=
  Finset.sum n.divisors fun d => ((1 : ℝ) / (d : ℝ)) ^ 2

noncomputable def conclusion_divisor_compressed_qaxis_hilbert_boundedness_zeta2_majorant
    (D : conclusion_divisor_compressed_qaxis_hilbert_boundedness_data) : ℝ :=
  Finset.sum (conclusion_divisor_compressed_qaxis_hilbert_boundedness_axis D)
    fun d => ((1 : ℝ) / (d : ℝ)) ^ 2

def conclusion_divisor_compressed_qaxis_hilbert_boundedness_statement
    (D : conclusion_divisor_compressed_qaxis_hilbert_boundedness_data) : Prop :=
  ∀ n ∈ conclusion_divisor_compressed_qaxis_hilbert_boundedness_axis D,
    (conclusion_divisor_compressed_qaxis_hilbert_boundedness_operator D n) ^ 2 ≤
      conclusion_divisor_compressed_qaxis_hilbert_boundedness_zeta2_majorant D *
        conclusion_divisor_compressed_qaxis_hilbert_boundedness_local_energy D n

lemma conclusion_divisor_compressed_qaxis_hilbert_boundedness_pointwise_bound
    (D : conclusion_divisor_compressed_qaxis_hilbert_boundedness_data) {n : ℕ}
    (_hn : n ∈ conclusion_divisor_compressed_qaxis_hilbert_boundedness_axis D) :
    (conclusion_divisor_compressed_qaxis_hilbert_boundedness_operator D n) ^ 2 ≤
      conclusion_divisor_compressed_qaxis_hilbert_boundedness_divisor_weight n *
        conclusion_divisor_compressed_qaxis_hilbert_boundedness_local_energy D n := by
  have htri :
      |conclusion_divisor_compressed_qaxis_hilbert_boundedness_operator D n| ≤
        Finset.sum n.divisors (fun d => |D.signal d / (d : ℝ)|) := by
    simpa [conclusion_divisor_compressed_qaxis_hilbert_boundedness_operator] using
      (Finset.abs_sum_le_sum_abs (s := n.divisors) (f := fun d => D.signal d / (d : ℝ)))
  have hsum_nonneg :
      0 ≤ Finset.sum n.divisors (fun d => |D.signal d / (d : ℝ)|) := by
    exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have htri_sq :
      |conclusion_divisor_compressed_qaxis_hilbert_boundedness_operator D n| ^ 2 ≤
        (Finset.sum n.divisors fun d => |D.signal d / (d : ℝ)|) ^ 2 := by
    have habs_nonneg :
        0 ≤ |conclusion_divisor_compressed_qaxis_hilbert_boundedness_operator D n| :=
      abs_nonneg _
    nlinarith
  have habs_eq :
      (Finset.sum n.divisors fun d => |D.signal d / (d : ℝ)|) =
        Finset.sum n.divisors fun d => |D.signal d| * ((1 : ℝ) / (d : ℝ)) := by
    refine Finset.sum_congr rfl ?_
    intro d hd
    rw [abs_div]
    rw [div_eq_mul_inv]
    simp [abs_of_nonneg, Nat.cast_nonneg]
  calc
    (conclusion_divisor_compressed_qaxis_hilbert_boundedness_operator D n) ^ 2
      = |conclusion_divisor_compressed_qaxis_hilbert_boundedness_operator D n| ^ 2 := by
          rw [sq_abs]
    _ ≤ (Finset.sum n.divisors fun d => |D.signal d / (d : ℝ)|) ^ 2 := htri_sq
    _ = (Finset.sum n.divisors fun d => |D.signal d| * ((1 : ℝ) / (d : ℝ))) ^ 2 := by
          rw [habs_eq]
    _ ≤
        (Finset.sum n.divisors fun d => |D.signal d| ^ 2) *
          Finset.sum n.divisors (fun d => (((1 : ℝ) / (d : ℝ)) ^ 2)) := by
            simpa using
              (Finset.sum_mul_sq_le_sq_mul_sq (s := n.divisors)
                (fun d => |D.signal d|) (fun d => ((1 : ℝ) / (d : ℝ))))
    _ =
        conclusion_divisor_compressed_qaxis_hilbert_boundedness_divisor_weight n *
          conclusion_divisor_compressed_qaxis_hilbert_boundedness_local_energy D n := by
            rw [conclusion_divisor_compressed_qaxis_hilbert_boundedness_divisor_weight,
              conclusion_divisor_compressed_qaxis_hilbert_boundedness_local_energy]
            ring

lemma conclusion_divisor_compressed_qaxis_hilbert_boundedness_divisor_weight_le_zeta2_majorant
    (D : conclusion_divisor_compressed_qaxis_hilbert_boundedness_data) {n : ℕ}
    (hn : n ∈ conclusion_divisor_compressed_qaxis_hilbert_boundedness_axis D) :
    conclusion_divisor_compressed_qaxis_hilbert_boundedness_divisor_weight n ≤
      conclusion_divisor_compressed_qaxis_hilbert_boundedness_zeta2_majorant D := by
  have hsubset :
      n.divisors ⊆ conclusion_divisor_compressed_qaxis_hilbert_boundedness_axis D := by
    intro d hd
    rcases Finset.mem_Icc.mp hn with ⟨hn1, hnq⟩
    have hdvd : d ∣ n := (Nat.mem_divisors.mp hd).1
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hn1
    have hdle : d ≤ n := Nat.le_of_dvd hn1 hdvd
    exact Finset.mem_Icc.mpr ⟨hdpos, hdle.trans hnq⟩
  refine Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_
  intro d hdaxis hdnotdiv
  positivity

theorem paper_conclusion_divisor_compressed_qaxis_hilbert_boundedness
    (D : conclusion_divisor_compressed_qaxis_hilbert_boundedness_data) :
    conclusion_divisor_compressed_qaxis_hilbert_boundedness_statement D := by
  intro n hn
  refine (conclusion_divisor_compressed_qaxis_hilbert_boundedness_pointwise_bound D hn).trans ?_
  have hweight :
      conclusion_divisor_compressed_qaxis_hilbert_boundedness_divisor_weight n ≤
        conclusion_divisor_compressed_qaxis_hilbert_boundedness_zeta2_majorant D :=
    conclusion_divisor_compressed_qaxis_hilbert_boundedness_divisor_weight_le_zeta2_majorant D hn
  exact mul_le_mul_of_nonneg_right hweight <| by
    simpa [conclusion_divisor_compressed_qaxis_hilbert_boundedness_local_energy] using
      (Finset.sum_nonneg fun d _ => sq_nonneg |D.signal d|)

end Omega.Conclusion
