import Mathlib.Tactic

namespace Omega.Zeta

private lemma xi_time_part9xaad_window6_constrained_wulff_saturation_value_cases
    {d : Fin 21 → ℕ} (hlo : ∀ i, 2 ≤ d i) (hhi : ∀ i, d i ≤ 4) (i : Fin 21) :
    d i = 2 ∨ d i = 3 ∨ d i = 4 := by
  have hlo_i := hlo i
  have hhi_i := hhi i
  omega

/-- Paper label: `thm:xi-time-part9xaad-window6-constrained-wulff-saturation`. -/
theorem paper_xi_time_part9xaad_window6_constrained_wulff_saturation
    (d : Fin 21 → ℕ) (hlo : ∀ i, 2 ≤ d i) (hhi : ∀ i, d i ≤ 4)
    (htwo : (Finset.univ.filter (fun i : Fin 21 => d i = 2)).card = 8)
    (hsum : (∑ i : Fin 21, d i) = 64) :
    (Finset.univ.filter (fun i : Fin 21 => d i = 3)).card = 4 ∧
      (Finset.univ.filter (fun i : Fin 21 => d i = 4)).card = 9 := by
  classical
  let c3 := (Finset.univ.filter (fun i : Fin 21 => d i = 3)).card
  let c4 := (Finset.univ.filter (fun i : Fin 21 => d i = 4)).card
  have hcount_decomp :
      (∑ i : Fin 21,
          ((if d i = 2 then 1 else 0) +
            (if d i = 3 then 1 else 0) +
              (if d i = 4 then 1 else 0))) = 21 := by
    calc
      (∑ i : Fin 21,
          ((if d i = 2 then 1 else 0) +
            (if d i = 3 then 1 else 0) +
              (if d i = 4 then 1 else 0))) = ∑ _i : Fin 21, 1 := by
            refine Finset.sum_congr rfl ?_
            intro i _
            rcases xi_time_part9xaad_window6_constrained_wulff_saturation_value_cases hlo hhi i
              with h | h | h <;> simp [h]
      _ = 21 := by norm_num
  have htwo_count : (∑ i : Fin 21, if d i = 2 then 1 else 0) = 8 := by
    rw [← Finset.sum_filter]
    simpa using htwo
  have hthree_count : (∑ i : Fin 21, if d i = 3 then 1 else 0) = c3 := by
    rw [← Finset.sum_filter]
    simp [c3]
  have hfour_count : (∑ i : Fin 21, if d i = 4 then 1 else 0) = c4 := by
    rw [← Finset.sum_filter]
    simp [c4]
  have hcard_eq : 8 + c3 + c4 = 21 := by
    simpa [Finset.sum_add_distrib, htwo_count, hthree_count, hfour_count]
      using hcount_decomp
  have hsum_decomp :
      (∑ i : Fin 21,
          ((if d i = 2 then 2 else 0) +
            (if d i = 3 then 3 else 0) +
              (if d i = 4 then 4 else 0))) = 64 := by
    calc
      (∑ i : Fin 21,
          ((if d i = 2 then 2 else 0) +
            (if d i = 3 then 3 else 0) +
              (if d i = 4 then 4 else 0))) = ∑ i : Fin 21, d i := by
            refine Finset.sum_congr rfl ?_
            intro i _
            rcases xi_time_part9xaad_window6_constrained_wulff_saturation_value_cases hlo hhi i
              with h | h | h <;> simp [h]
      _ = 64 := hsum
  have htwo_weight : (∑ i : Fin 21, if d i = 2 then 2 else 0) = 16 := by
    rw [← Finset.sum_filter]
    simp [htwo]
  have hthree_weight : (∑ i : Fin 21, if d i = 3 then 3 else 0) = 3 * c3 := by
    rw [← Finset.sum_filter]
    simp [c3, mul_comm]
  have hfour_weight : (∑ i : Fin 21, if d i = 4 then 4 else 0) = 4 * c4 := by
    rw [← Finset.sum_filter]
    simp [c4, mul_comm]
  have hsum_eq : 16 + 3 * c3 + 4 * c4 = 64 := by
    simpa [Finset.sum_add_distrib, htwo_weight, hthree_weight, hfour_weight]
      using hsum_decomp
  have hc3 : c3 = 4 := by omega
  have hc4 : c4 = 9 := by omega
  exact ⟨hc3, hc4⟩

end Omega.Zeta
