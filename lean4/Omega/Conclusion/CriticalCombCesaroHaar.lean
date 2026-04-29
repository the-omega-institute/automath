import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- The nonzero Fourier coefficient of the `q`-th comb measure is the divisibility indicator
`1_{q ∣ n}`. -/
def conclusion_critical_comb_cesaro_haar_fourierCoeff (q n : ℕ) : ℕ :=
  if q ∣ n then 1 else 0

/-- The Haar coefficient is `1` at frequency `0` and `0` otherwise. -/
def conclusion_critical_comb_cesaro_haar_haarCoeff (n : ℕ) : ℝ :=
  if n = 0 then 1 else 0

/-- Cesàro average of the explicit comb Fourier coefficients. -/
noncomputable def conclusion_critical_comb_cesaro_haar_cesaroAverage (Q n : ℕ) : ℝ :=
  ((Finset.sum (Finset.Icc 1 Q) fun q =>
      conclusion_critical_comb_cesaro_haar_fourierCoeff q n : ℕ) : ℝ) / Q

private lemma conclusion_critical_comb_cesaro_haar_indicator_sum_eq_card (Q n : ℕ) :
    Finset.sum (Finset.Icc 1 Q) (fun q => conclusion_critical_comb_cesaro_haar_fourierCoeff q n) =
      ((Finset.Icc 1 Q).filter fun q => q ∣ n).card := by
  simp [conclusion_critical_comb_cesaro_haar_fourierCoeff]

private lemma conclusion_critical_comb_cesaro_haar_divisor_count_bound (Q n : ℕ) (hn : 0 < n) :
    Finset.sum (Finset.Icc 1 Q) (fun q => conclusion_critical_comb_cesaro_haar_fourierCoeff q n) ≤
      n + 1 := by
  rw [conclusion_critical_comb_cesaro_haar_indicator_sum_eq_card]
  have hsubset :
      ((Finset.Icc 1 Q).filter fun q => q ∣ n) ⊆ Finset.range (n + 1) := by
    intro q hq
    rw [Finset.mem_filter] at hq
    rcases hq with ⟨hqIcc, hqdiv⟩
    have hqIcc' : 1 ≤ q ∧ q ≤ Q := by
      rwa [Finset.mem_Icc] at hqIcc
    exact Finset.mem_range.mpr (lt_of_le_of_lt (Nat.le_of_dvd hn hqdiv) (Nat.lt_succ_self n))
  calc
    ((Finset.Icc 1 Q).filter fun q => q ∣ n).card ≤ (Finset.range (n + 1)).card :=
      Finset.card_le_card hsubset
    _ = n + 1 := by simp

/-- Paper label: `thm:conclusion-critical-comb-cesaro-haar`. The explicit Fourier coefficient of
the `q`-th comb is the divisibility indicator `1_{q ∣ n}`; averaging over `q ≤ Q` kills every
nonzero mode by the divisor bound, while the zero mode stays equal to `1`. The strict RH gap
converse is the immediate contradiction `|μ| < √λ` versus `|μ| = √λ`. -/
theorem paper_conclusion_critical_comb_cesaro_haar :
    (∀ q n : ℕ,
      conclusion_critical_comb_cesaro_haar_fourierCoeff q n = if q ∣ n then 1 else 0) ∧
      (∀ n : ℕ, ∀ ε > 0, ∃ N : ℕ, ∀ Q ≥ N,
        |conclusion_critical_comb_cesaro_haar_cesaroAverage Q n -
            conclusion_critical_comb_cesaro_haar_haarCoeff n| < ε) ∧
      (∀ lam : ℝ, ∀ μ : ℝ, 1 < lam → |μ| < Real.sqrt lam → ¬ (|μ| = Real.sqrt lam)) := by
  refine ⟨fun q n => rfl, ?_, ?_⟩
  · intro n ε hε
    by_cases hn : n = 0
    · refine ⟨1, ?_⟩
      intro Q hQ
      have hQpos : 0 < Q := lt_of_lt_of_le (by decide : 0 < 1) hQ
      have hsum :
          Finset.sum (Finset.Icc 1 Q) (fun q => conclusion_critical_comb_cesaro_haar_fourierCoeff q 0) =
            Q := by
        simp [conclusion_critical_comb_cesaro_haar_fourierCoeff]
      have havg : conclusion_critical_comb_cesaro_haar_cesaroAverage Q 0 = 1 := by
        unfold conclusion_critical_comb_cesaro_haar_cesaroAverage
        rw [hsum]
        have hQne : (Q : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hQpos
        rw [div_self hQne]
      simp [conclusion_critical_comb_cesaro_haar_haarCoeff, hn, havg, hε]
    · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
      obtain ⟨N, hN⟩ := exists_nat_gt (((n + 1 : ℕ) : ℝ) / ε)
      refine ⟨max N 1, ?_⟩
      intro Q hQ
      have hQgeN : N ≤ Q := le_trans (le_max_left N 1) hQ
      have hQge1 : 1 ≤ Q := le_trans (le_max_right N 1) hQ
      have hQpos : 0 < Q := lt_of_lt_of_le (by decide : 0 < 1) hQge1
      have hsum_nat :
          Finset.sum (Finset.Icc 1 Q) (fun q => conclusion_critical_comb_cesaro_haar_fourierCoeff q n) ≤
            n + 1 :=
        conclusion_critical_comb_cesaro_haar_divisor_count_bound Q n hn_pos
      have hsum_real :
          ((Finset.sum (Finset.Icc 1 Q)
              fun q => conclusion_critical_comb_cesaro_haar_fourierCoeff q n : ℕ) : ℝ) ≤
            (((n + 1 : ℕ) : ℝ)) := by
        exact_mod_cast hsum_nat
      have havg_nonneg : 0 ≤ conclusion_critical_comb_cesaro_haar_cesaroAverage Q n := by
        unfold conclusion_critical_comb_cesaro_haar_cesaroAverage
        positivity
      have hratio :
          conclusion_critical_comb_cesaro_haar_cesaroAverage Q n ≤ ((n + 1 : ℕ) : ℝ) / Q := by
        unfold conclusion_critical_comb_cesaro_haar_cesaroAverage
        exact div_le_div_of_nonneg_right hsum_real (by positivity)
      have hQN :
          (((n + 1 : ℕ) : ℝ) / Q) ≤ (((n + 1 : ℕ) : ℝ) / max N 1) := by
        have hQinv : 1 / (Q : ℝ) ≤ 1 / (max N 1 : ℝ) := by
          apply one_div_le_one_div_of_le
          · positivity
          · exact_mod_cast hQ
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
          mul_le_mul_of_nonneg_left hQinv (by positivity : 0 ≤ (((n + 1 : ℕ) : ℝ)))
      have hNlt : (((n + 1 : ℕ) : ℝ) / ε) < ((max N 1 : ℕ) : ℝ) := by
        exact lt_of_lt_of_le hN (by exact_mod_cast le_max_left N 1)
      have hsmall : (((n + 1 : ℕ) : ℝ) / ((max N 1 : ℕ) : ℝ)) < ε := by
        have hNlt' : ((n : ℝ) + 1) / ε < max (N : ℝ) 1 := by
          simpa [Nat.cast_add] using hNlt
        have hnum : (n : ℝ) + 1 < max (N : ℝ) 1 * ε := by
          exact (div_lt_iff₀ hε).mp hNlt'
        have hden : 0 < max (N : ℝ) 1 := by positivity
        have hsmall' : ((n : ℝ) + 1) / max (N : ℝ) 1 < ε := by
          exact (div_lt_iff₀ hden).2 (by simpa [mul_comm] using hnum)
        simpa [Nat.cast_add] using hsmall'
      have hhaar : conclusion_critical_comb_cesaro_haar_haarCoeff n = 0 := by
        simp [conclusion_critical_comb_cesaro_haar_haarCoeff, hn]
      rw [hhaar, sub_zero, abs_of_nonneg havg_nonneg]
      exact lt_of_le_of_lt (le_trans hratio hQN) hsmall
  · intro lam μ hlam hμ heq
    let _ := hlam
    rw [heq] at hμ
    exact (lt_irrefl _ hμ)

end Omega.Conclusion
