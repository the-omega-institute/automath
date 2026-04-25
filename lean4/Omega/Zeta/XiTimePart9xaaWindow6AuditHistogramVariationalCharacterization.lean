import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

private theorem xi_time_part9xaa_window6_audit_histogram_variational_characterization_tangent
    (Phi : ℕ → ℝ)
    (hconv : ∀ a b : ℕ, 3 ≤ a → b + 2 ≤ a →
      Phi (a - 1) + Phi (b + 1) < Phi a + Phi b) :
    ∀ n : ℕ, 0 < n → n ≠ 2 →
      let L : ℕ → ℝ := fun k => (4 - (k : ℝ)) * Phi 3 + ((k : ℝ) - 3) * Phi 4
      L n ≤ Phi n ∧ (n ≠ 3 → n ≠ 4 → L n < Phi n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hn_pos hn_ne_two
      let L : ℕ → ℝ := fun k => (4 - (k : ℝ)) * Phi 3 + ((k : ℝ) - 3) * Phi 4
      by_cases hn1 : n = 1
      · subst n
        have h42 := hconv 4 2 (by norm_num) (by norm_num)
        have h41 := hconv 4 1 (by norm_num) (by norm_num)
        constructor
        · dsimp [L]
          norm_num at h42 h41 ⊢
          linarith
        · intro _h13 _h14
          dsimp [L]
          norm_num at h42 h41 ⊢
          linarith
      · by_cases hn3 : n = 3
        · subst n
          constructor
          · dsimp [L]
            norm_num
          · intro h33 _h34
            exact False.elim (h33 rfl)
        · by_cases hn4 : n = 4
          · subst n
            constructor
            · dsimp [L]
              norm_num
            · intro _h43 h44
              exact False.elim (h44 rfl)
          · have hn_ge_five : 5 ≤ n := by omega
            have hn_pred_pos : 0 < n - 1 := by omega
            have hn_pred_ne_two : n - 1 ≠ 2 := by omega
            have hpred := ih (n - 1) (by omega) hn_pred_pos hn_pred_ne_two
            have hstep := hconv n 3 (by omega) (by omega)
            have hLstep : L n = L (n - 1) - Phi 3 + Phi 4 := by
              have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
                simpa using (Nat.cast_sub (R := ℝ) (by omega : 1 ≤ n))
              dsimp [L]
              rw [hcast]
              ring
            have hstrict : L n < Phi n := by
              rw [hLstep]
              linarith [hpred.1, hstep]
            exact ⟨le_of_lt hstrict, fun _ _ => hstrict⟩

/-- Paper label:
`thm:xi-time-part9xaa-window6-audit-histogram-variational-characterization`. -/
theorem paper_xi_time_part9xaa_window6_audit_histogram_variational_characterization
    (Phi : ℕ → ℝ)
    (hconv : ∀ a b : ℕ, 3 ≤ a → b + 2 ≤ a →
      Phi (a - 1) + Phi (b + 1) < Phi a + Phi b)
    (d : Fin 21 → ℕ) (hpos : ∀ i, 0 < d i)
    (hsum : (Finset.univ.sum fun i => d i) = 64)
    (htwo : (Finset.univ.filter fun i => d i = 2).card = 8) :
    8 * Phi 2 + 4 * Phi 3 + 9 * Phi 4 ≤ Finset.univ.sum (fun i => Phi (d i)) ∧
      (Finset.univ.sum (fun i => Phi (d i)) = 8 * Phi 2 + 4 * Phi 3 + 9 * Phi 4 →
        (Finset.univ.filter fun i => d i = 3).card = 4 ∧
          (Finset.univ.filter fun i => d i = 4).card = 9) := by
  classical
  let T : Finset (Fin 21) := Finset.univ.filter fun i => d i = 2
  let R : Finset (Fin 21) := Finset.univ.filter fun i => d i ≠ 2
  let L : ℕ → ℝ := fun k => (4 - (k : ℝ)) * Phi 3 + ((k : ℝ) - 3) * Phi 4
  have hcardR : R.card = 13 := by
    have hpart :
        T.card + R.card = 21 := by
      simpa [T, R] using
        (Finset.card_filter_add_card_filter_not
          (s := (Finset.univ : Finset (Fin 21))) (p := fun i : Fin 21 => d i = 2))
    have hT : T.card = 8 := by simpa [T] using htwo
    omega
  have hsumT_nat : T.sum (fun i => d i) = 16 := by
    calc
      T.sum (fun i => d i) = T.sum (fun _ => 2) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        have hdi : d i = 2 := by simpa [T] using (Finset.mem_filter.mp hi).2
        simp [hdi]
      _ = 16 := by
        have hT : T.card = 8 := by simpa [T] using htwo
        simp [hT]
  have hsumR_nat : R.sum (fun i => d i) = 48 := by
    have hsplit :
        T.sum (fun i => d i) + R.sum (fun i => d i) = 64 := by
      have hsplit' :=
        (Finset.sum_filter_add_sum_filter_not
          (s := (Finset.univ : Finset (Fin 21))) (p := fun i : Fin 21 => d i = 2)
          (f := fun i : Fin 21 => d i))
      simpa [T, R, hsum] using hsplit'
    omega
  have hsumT_phi : T.sum (fun i => Phi (d i)) = 8 * Phi 2 := by
    calc
      T.sum (fun i => Phi (d i)) = T.sum (fun _ => Phi 2) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        have hdi : d i = 2 := by simpa [T] using (Finset.mem_filter.mp hi).2
        simp [hdi]
      _ = 8 * Phi 2 := by
        have hT : T.card = 8 := by simpa [T] using htwo
        simp [hT, mul_comm]
  have hsplit_phi :
      T.sum (fun i => Phi (d i)) + R.sum (fun i => Phi (d i)) =
        Finset.univ.sum (fun i : Fin 21 => Phi (d i)) := by
    simpa [T, R] using
      (Finset.sum_filter_add_sum_filter_not
        (s := (Finset.univ : Finset (Fin 21))) (p := fun i : Fin 21 => d i = 2)
        (f := fun i : Fin 21 => Phi (d i)))
  have hLsum : R.sum (fun i => L (d i)) = 4 * Phi 3 + 9 * Phi 4 := by
    have hcardR_real : (R.card : ℝ) = 13 := by exact_mod_cast hcardR
    have hsumR_real : ((R.sum fun i => d i) : ℝ) = 48 := by exact_mod_cast hsumR_nat
    have hsum_cast : R.sum (fun i => (d i : ℝ)) = ((R.sum fun i => d i) : ℝ) := by
      exact_mod_cast rfl
    have hsum_four : R.sum (fun _ : Fin 21 => (4 : ℝ)) = 4 * (R.card : ℝ) := by
      simp [mul_comm]
    have hsum_three : R.sum (fun _ : Fin 21 => (3 : ℝ)) = 3 * (R.card : ℝ) := by
      simp [mul_comm]
    calc
      R.sum (fun i => L (d i))
          =
            (4 * (R.card : ℝ) - ((R.sum fun i => d i) : ℝ)) * Phi 3 +
              (((R.sum fun i => d i) : ℝ) - 3 * (R.card : ℝ)) * Phi 4 := by
            rw [show R.sum (fun i => L (d i)) =
                R.sum (fun i => ((4 : ℝ) - (d i : ℝ)) * Phi 3) +
                  R.sum (fun i => (((d i : ℝ) - 3) * Phi 4)) by
                simp [L, Finset.sum_add_distrib]]
            rw [← Finset.sum_mul, ← Finset.sum_mul, Finset.sum_sub_distrib,
              Finset.sum_sub_distrib, hsum_four, hsum_three, hsum_cast]
      _ = 4 * Phi 3 + 9 * Phi 4 := by
            rw [hcardR_real, hsumR_real]
            ring
  have htangent := xi_time_part9xaa_window6_audit_histogram_variational_characterization_tangent
    Phi hconv
  have hR_lower : R.sum (fun i => L (d i)) ≤ R.sum (fun i => Phi (d i)) := by
    refine Finset.sum_le_sum ?_
    intro i hi
    have hne : d i ≠ 2 := by simpa [R] using (Finset.mem_filter.mp hi).2
    exact (htangent (d i) (hpos i) hne).1
  constructor
  · calc
      8 * Phi 2 + 4 * Phi 3 + 9 * Phi 4
          = T.sum (fun i => Phi (d i)) + R.sum (fun i => L (d i)) := by
              rw [hsumT_phi, hLsum]
              ring
      _ ≤ T.sum (fun i => Phi (d i)) + R.sum (fun i => Phi (d i)) := by
              linarith
      _ = Finset.univ.sum (fun i : Fin 21 => Phi (d i)) := hsplit_phi
  · intro hEq
    have hgap_nonneg :
        ∀ i ∈ R, 0 ≤ Phi (d i) - L (d i) := by
      intro i hi
      have hne : d i ≠ 2 := by simpa [R] using (Finset.mem_filter.mp hi).2
      have hle := (htangent (d i) (hpos i) hne).1
      linarith
    have hgap_sum : R.sum (fun i => Phi (d i) - L (d i)) = 0 := by
      have hsplit_gap :
          R.sum (fun i => Phi (d i) - L (d i)) =
            R.sum (fun i => Phi (d i)) - R.sum (fun i => L (d i)) := by
        rw [Finset.sum_sub_distrib]
      rw [hsplit_gap]
      linarith [hEq, hsplit_phi, hsumT_phi, hLsum]
    have hgap_zero :=
      (Finset.sum_eq_zero_iff_of_nonneg hgap_nonneg).mp hgap_sum
    have hR_values : ∀ i ∈ R, d i = 3 ∨ d i = 4 := by
      intro i hi
      have hne : d i ≠ 2 := by simpa [R] using (Finset.mem_filter.mp hi).2
      have hstrict_or := (htangent (d i) (hpos i) hne).2
      by_contra hnot
      have hne3 : d i ≠ 3 := by
        intro h3
        exact hnot (Or.inl h3)
      have hne4 : d i ≠ 4 := by
        intro h4
        exact hnot (Or.inr h4)
      have hstrict : L (d i) < Phi (d i) := hstrict_or hne3 hne4
      have hzero := hgap_zero i hi
      linarith
    let A3 : Finset (Fin 21) := Finset.univ.filter fun i => d i = 3
    let A4 : Finset (Fin 21) := Finset.univ.filter fun i => d i = 4
    have hR_eq : R = A3 ∪ A4 := by
      ext i
      constructor
      · intro hi
        rcases hR_values i hi with h3 | h4
        · exact Finset.mem_union.mpr (Or.inl (by simp [A3, h3]))
        · exact Finset.mem_union.mpr (Or.inr (by simp [A4, h4]))
      · intro hi
        rcases Finset.mem_union.mp hi with hi3 | hi4
        · have h3 : d i = 3 := by simpa [A3] using (Finset.mem_filter.mp hi3).2
          simp [R, h3]
        · have h4 : d i = 4 := by simpa [A4] using (Finset.mem_filter.mp hi4).2
          simp [R, h4]
    have hdisj : Disjoint A3 A4 := by
      refine Finset.disjoint_left.mpr ?_
      intro i hi3 hi4
      have h3 : d i = 3 := by simpa [A3] using (Finset.mem_filter.mp hi3).2
      have h4 : d i = 4 := by simpa [A4] using (Finset.mem_filter.mp hi4).2
      omega
    have hcard34 : A3.card + A4.card = 13 := by
      have hcard_union : (A3 ∪ A4).card = A3.card + A4.card := by
        exact Finset.card_union_of_disjoint hdisj
      rw [← hR_eq] at hcard_union
      omega
    have hsum34 : 3 * A3.card + 4 * A4.card = 48 := by
      have hsum_union :
          (A3 ∪ A4).sum (fun i => d i) = A3.sum (fun i => d i) + A4.sum (fun i => d i) := by
        exact Finset.sum_union hdisj
      have hsumA3 : A3.sum (fun i => d i) = A3.card * 3 := by
        calc
          A3.sum (fun i => d i) = A3.sum (fun _ => 3) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            have h3 : d i = 3 := by simpa [A3] using (Finset.mem_filter.mp hi).2
            simp [h3]
          _ = A3.card * 3 := by simp
      have hsumA4 : A4.sum (fun i => d i) = A4.card * 4 := by
        calc
          A4.sum (fun i => d i) = A4.sum (fun _ => 4) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            have h4 : d i = 4 := by simpa [A4] using (Finset.mem_filter.mp hi).2
            simp [h4]
          _ = A4.card * 4 := by simp
      rw [← hR_eq, hsumR_nat, hsumA3, hsumA4] at hsum_union
      omega
    have hA3 : A3.card = 4 := by omega
    have hA4 : A4.card = 9 := by omega
    exact ⟨by simpa [A3] using hA3, by simpa [A4] using hA4⟩

end Omega.Zeta
