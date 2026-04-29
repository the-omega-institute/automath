import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-uniform-complete-graph-generator`. -/
theorem paper_conclusion_uniform_complete_graph_generator (n : ℕ) (hn : 2 ≤ n) :
    let Q : Fin n → Fin n → ℝ := fun i j => if i = j then -1 else ((n - 1 : ℝ)⁻¹)
    (∀ i, (∑ j, Q i j) = 0) ∧
      (∀ v : Fin n → ℝ, (∑ j, v j) = 0 → ∀ i,
        (∑ j, Q i j * v j) = -((n : ℝ) / (n - 1)) * v i) := by
  classical
  intro Q
  have hn_ne_zero : (n : ℝ) - 1 ≠ 0 := by
    intro h
    have hn_one : (n : ℝ) = 1 := sub_eq_zero.mp h
    have : n = 1 := by exact_mod_cast hn_one
    omega
  constructor
  · intro i
    have hsum :
        (∑ j : Fin n, Q i j) =
          -1 + ∑ j ∈ ({i}ᶜ : Finset (Fin n)), ((n - 1 : ℝ)⁻¹) := by
      calc
        (∑ j : Fin n, Q i j) =
            Q i i + ∑ j ∈ ({i}ᶜ : Finset (Fin n)), Q i j := by
          rw [Fintype.sum_eq_add_sum_compl i (fun j => Q i j)]
        _ = -1 + ∑ j ∈ ({i}ᶜ : Finset (Fin n)), ((n - 1 : ℝ)⁻¹) := by
          congr 1
          · simp [Q]
          · refine Finset.sum_congr rfl ?_
            intro j hj
            have hne : i ≠ j := by
              simpa [eq_comm] using hj
            simp [Q, hne]
    rw [hsum]
    have hcard : ({i}ᶜ : Finset (Fin n)).card = n - 1 := by
      simp [Finset.card_compl]
    rw [Finset.sum_const, hcard]
    rw [nsmul_eq_mul]
    have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      simpa using (Nat.cast_sub (R := ℝ) (by omega : 1 ≤ n))
    rw [hcast]
    field_simp [hn_ne_zero]
    norm_num
  · intro v hv i
    have hsum :
        (∑ j : Fin n, Q i j * v j) =
          -v i + ((n - 1 : ℝ)⁻¹) * ∑ j ∈ ({i}ᶜ : Finset (Fin n)), v j := by
      calc
        (∑ j : Fin n, Q i j * v j) =
            Q i i * v i + ∑ j ∈ ({i}ᶜ : Finset (Fin n)), Q i j * v j := by
          rw [Fintype.sum_eq_add_sum_compl i (fun j => Q i j * v j)]
        _ = -v i + ∑ j ∈ ({i}ᶜ : Finset (Fin n)), ((n - 1 : ℝ)⁻¹) * v j := by
          congr 1
          · simp [Q]
          · refine Finset.sum_congr rfl ?_
            intro j hj
            have hne : i ≠ j := by
              simpa [eq_comm] using hj
            simp [Q, hne]
        _ = -v i + ((n - 1 : ℝ)⁻¹) * ∑ j ∈ ({i}ᶜ : Finset (Fin n)), v j := by
          rw [Finset.mul_sum]
    have hcompl : (∑ j ∈ ({i}ᶜ : Finset (Fin n)), v j) = -v i := by
      have hsplit := Fintype.sum_eq_add_sum_compl i v
      rw [hv] at hsplit
      linarith
    rw [hsum, hcompl]
    field_simp [hn_ne_zero]
    ring

end Omega.Conclusion
