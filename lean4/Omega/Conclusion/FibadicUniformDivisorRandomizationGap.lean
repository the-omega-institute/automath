import Mathlib

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-fibadic-uniform-divisor-randomization-gap`. A maximizing index
for the exponents simultaneously maximizes `x / (x + 1)` and minimizes `1 / (x + 1)`. -/
theorem paper_conclusion_fibadic_uniform_divisor_randomization_gap {r : ℕ} (hr : 0 < r)
    (a : Fin r → ℕ) :
    ∃ jmax jmin : Fin r,
      (forall j, (a j : ℝ) / (a j + 1) <= (a jmax : ℝ) / (a jmax + 1)) ∧
      (forall j, (1 : ℝ) / (a jmin + 1) <= (1 : ℝ) / (a j + 1)) ∧
      1 - (a jmax : ℝ) / (a jmax + 1) = (1 : ℝ) / (a jmin + 1) := by
  let _ : Nonempty (Fin r) := Fin.pos_iff_nonempty.mp hr
  let hnonempty : (Finset.univ : Finset (Fin r)).Nonempty := Finset.univ_nonempty
  rcases Finset.exists_max_image (Finset.univ : Finset (Fin r)) a hnonempty with
    ⟨jmax, -, hjmax⟩
  refine ⟨jmax, jmax, ?_, ?_, ?_⟩
  · intro j
    have hle_nat : a j ≤ a jmax := hjmax j (by simp)
    have hj_pos : 0 < (a j : ℝ) + 1 := by positivity
    have hmax_pos : 0 < (a jmax : ℝ) + 1 := by positivity
    have hstep : (a j : ℝ) + 1 ≤ (a jmax : ℝ) + 1 := by
      exact_mod_cast Nat.succ_le_succ hle_nat
    have hrecip : (1 : ℝ) / (a jmax + 1) ≤ (1 : ℝ) / (a j + 1) :=
      one_div_le_one_div_of_le hj_pos hstep
    have hratio_j : (a j : ℝ) / (a j + 1) = 1 - (1 : ℝ) / (a j + 1) := by
      field_simp [hj_pos.ne']
      ring_nf
    have hratio_max : (a jmax : ℝ) / (a jmax + 1) = 1 - (1 : ℝ) / (a jmax + 1) := by
      field_simp [hmax_pos.ne']
      ring_nf
    rw [hratio_j, hratio_max]
    nlinarith
  · intro j
    have hle_nat : a j ≤ a jmax := hjmax j (by simp)
    have hstep : (a j : ℝ) + 1 ≤ (a jmax : ℝ) + 1 := by
      exact_mod_cast Nat.succ_le_succ hle_nat
    have hj_pos : 0 < (a j : ℝ) + 1 := by positivity
    exact one_div_le_one_div_of_le hj_pos hstep
  · have hmax_pos : 0 < (a jmax : ℝ) + 1 := by positivity
    have hratio_max : (a jmax : ℝ) / (a jmax + 1) = 1 - (1 : ℝ) / (a jmax + 1) := by
      field_simp [hmax_pos.ne']
      ring_nf
    rw [hratio_max]
    ring

end Omega.Conclusion
