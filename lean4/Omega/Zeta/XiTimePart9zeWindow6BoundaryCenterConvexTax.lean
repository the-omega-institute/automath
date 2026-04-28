import Mathlib.Tactic

namespace Omega.Zeta

lemma xi_time_part9ze_window6_boundary_center_convex_tax_int_sq_lower
    (n : ℕ) (hn : 0 < n) : (7 : ℤ) * (n : ℤ) - 12 ≤ (n : ℤ) ^ 2 := by
  by_cases hsmall : n ≤ 4
  · interval_cases n <;> norm_num at hn ⊢
  · have hn5 : (5 : ℤ) ≤ (n : ℤ) := by
      have : 5 ≤ n := by omega
      exact_mod_cast this
    have hsq : 0 ≤ ((n : ℤ) - 4) ^ 2 := sq_nonneg _
    nlinarith

/-- Paper label: `cor:xi-time-part9ze-window6-boundary-center-convex-tax`. -/
theorem paper_xi_time_part9ze_window6_boundary_center_convex_tax
    (d : Fin 21 → ℕ)
    (hSum : (Finset.univ.sum fun i => d i) = 64)
    (hPos : ∀ i, 0 < d i)
    (hTwo : ∃ S : Finset (Fin 21), S.card = 3 ∧ ∀ i ∈ S, d i = 2) :
    202 ≤ Finset.univ.sum (fun i => d i ^ 2) := by
  rcases hTwo with ⟨S, hScard, hS⟩
  have hPoint :
      ∀ i : Fin 21,
        (7 : ℤ) * (d i : ℤ) - 12 + (if i ∈ S then (2 : ℤ) else 0)
          ≤ (d i : ℤ) ^ 2 := by
    intro i
    by_cases hi : i ∈ S
    · have hdi : d i = 2 := hS i hi
      simp [hdi, hi]
    · simpa [hi] using
        xi_time_part9ze_window6_boundary_center_convex_tax_int_sq_lower (d i) (hPos i)
  have hLower :
      (Finset.univ.sum fun i : Fin 21 =>
          (7 : ℤ) * (d i : ℤ) - 12 + (if i ∈ S then (2 : ℤ) else 0))
        ≤ Finset.univ.sum (fun i : Fin 21 => (d i : ℤ) ^ 2) :=
    Finset.sum_le_sum fun i _ => hPoint i
  have hSumInt : (Finset.univ.sum fun i : Fin 21 => (d i : ℤ)) = 64 := by
    exact_mod_cast hSum
  have hIndicator :
      (Finset.univ.sum fun i : Fin 21 => if i ∈ S then (2 : ℤ) else 0) = 6 := by
    rw [← Finset.sum_filter]
    have hFilter : Finset.univ.filter (fun i : Fin 21 => i ∈ S) = S := by
      ext i
      simp
    simp [hFilter, hScard]
  have hWeighted : (Finset.univ.sum fun i : Fin 21 => (7 : ℤ) * (d i : ℤ)) = 448 := by
    rw [← Finset.mul_sum, hSumInt]
    norm_num
  have hBase :
      (Finset.univ.sum fun i : Fin 21 =>
          (7 : ℤ) * (d i : ℤ) - 12 + (if i ∈ S then (2 : ℤ) else 0)) = 202 := by
    simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, hWeighted,
      hIndicator]
  have hCast :
      (202 : ℤ) ≤ (Finset.univ.sum (fun i : Fin 21 => d i ^ 2) : ℤ) := by
    simpa [hBase, Nat.cast_sum, Nat.cast_pow] using hLower
  exact_mod_cast hCast

end Omega.Zeta
