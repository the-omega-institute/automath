import Mathlib

namespace Omega.DerivedConsequences

open scoped BigOperators

/-- The normalized residue-class partial sum `∑_{n ≤ N} N_{n,r}^{(m)} / λ^n`. -/
noncomputable def derived_congruence_bias_finitepart_localization_partialSum {m : ℕ}
    (lambda : ℝ) (counts : ℕ → Fin m → ℝ) (r : Fin m) (N : ℕ) : ℝ :=
  Finset.sum (Finset.Icc 1 N) fun n => counts n r / lambda ^ n

/-- The parity bias `B_n = N_{n,0}^{(2)} - N_{n,1}^{(2)}`. -/
noncomputable def derived_congruence_bias_finitepart_localization_bias
    (counts : ℕ → Fin 2 → ℝ) (n : ℕ) : ℝ :=
  counts n 0 - counts n 1

/-- Paper label: `thm:derived-congruence-bias-finitepart-localization`.
If every residue class has the same logarithmic main term and only differs by its finite-part
constant, then subtracting two residue classes isolates those constants exactly. In the parity case,
combining the recorded `ρ^n / n` bias bound with a Perron lower bound `λ^n / n ≤ p_n` yields an
exponentially decaying bias ratio. -/
theorem paper_derived_congruence_bias_finitepart_localization {m : ℕ}
    (hm : 0 < m) (lambda rho : ℝ) (counts : ℕ → Fin m → ℝ) (finitePart : Fin m → ℝ)
    (hpartial :
      ∀ N, 1 ≤ N →
        ∀ r : Fin m,
          derived_congruence_bias_finitepart_localization_partialSum lambda counts r N =
            (1 / (m : ℝ)) * Real.log N + finitePart r)
    (parityCounts : ℕ → Fin 2 → ℝ) (primitiveCount : ℕ → ℝ)
    (hbias :
      ∀ n, 1 ≤ n →
        |derived_congruence_bias_finitepart_localization_bias parityCounts n| ≤ rho ^ n / n)
    (hprimitive :
      ∀ n, 1 ≤ n → lambda ^ n / n ≤ primitiveCount n)
    (hlambda : 0 < lambda) (hrho : 0 ≤ rho) :
    (∀ N, 1 ≤ N →
      ∀ r s : Fin m,
        derived_congruence_bias_finitepart_localization_partialSum lambda counts r N -
            derived_congruence_bias_finitepart_localization_partialSum lambda counts s N =
          finitePart r - finitePart s) ∧
      ∀ n, 1 ≤ n →
        |derived_congruence_bias_finitepart_localization_bias parityCounts n / primitiveCount n| ≤
          (rho / lambda) ^ n := by
  refine ⟨?_, ?_⟩
  · intro N hN r s
    rw [hpartial N hN r, hpartial N hN s]
    ring
  · intro n hn
    have hn_real_pos : 0 < (n : ℝ) := by
      exact_mod_cast hn
    have hlambda_pow_pos : 0 < lambda ^ n := by
      positivity
    have hmain_pos : 0 < lambda ^ n / n := by
      exact div_pos hlambda_pow_pos hn_real_pos
    have hprimitive_pos : 0 < primitiveCount n := by
      exact lt_of_lt_of_le hmain_pos (hprimitive n hn)
    have habs :
        |derived_congruence_bias_finitepart_localization_bias parityCounts n / primitiveCount n| =
          |derived_congruence_bias_finitepart_localization_bias parityCounts n| / primitiveCount n := by
      rw [abs_div, abs_of_pos hprimitive_pos]
    have hstep₁ :
        |derived_congruence_bias_finitepart_localization_bias parityCounts n| / primitiveCount n ≤
          |derived_congruence_bias_finitepart_localization_bias parityCounts n| / (lambda ^ n / n) := by
      have hrecip : 1 / primitiveCount n ≤ 1 / (lambda ^ n / n) := by
        exact one_div_le_one_div_of_le hmain_pos (hprimitive n hn)
      calc
        |derived_congruence_bias_finitepart_localization_bias parityCounts n| / primitiveCount n =
            |derived_congruence_bias_finitepart_localization_bias parityCounts n| *
              (1 / primitiveCount n) := by
                simp [div_eq_mul_inv, one_div]
        _ ≤ |derived_congruence_bias_finitepart_localization_bias parityCounts n| *
              (1 / (lambda ^ n / n)) := by
                exact mul_le_mul_of_nonneg_left hrecip (abs_nonneg _)
        _ = |derived_congruence_bias_finitepart_localization_bias parityCounts n| /
              (lambda ^ n / n) := by
                simp [div_eq_mul_inv, one_div]
    have hstep₂ :
        |derived_congruence_bias_finitepart_localization_bias parityCounts n| / (lambda ^ n / n) ≤
          (rho ^ n / n) / (lambda ^ n / n) := by
      exact div_le_div_of_nonneg_right (hbias n hn) hmain_pos.le
    have hratio :
        (rho ^ n / n) / (lambda ^ n / n) = (rho / lambda) ^ n := by
      have hn_nat_pos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
      have hn_ne : (n : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt hn_nat_pos)
      have hlambda_ne : lambda ≠ 0 := ne_of_gt hlambda
      calc
        (rho ^ n / n) / (lambda ^ n / n) = (rho ^ n / n) * (n / lambda ^ n) := by
          rw [div_eq_mul_inv, inv_div]
        _ = rho ^ n / lambda ^ n := by
          field_simp [hn_ne, hlambda_ne]
        _ = (rho / lambda) ^ n := by
          rw [div_pow]
    calc
      |derived_congruence_bias_finitepart_localization_bias parityCounts n / primitiveCount n| =
          |derived_congruence_bias_finitepart_localization_bias parityCounts n| / primitiveCount n := habs
      _ ≤ |derived_congruence_bias_finitepart_localization_bias parityCounts n| / (lambda ^ n / n) :=
          hstep₁
      _ ≤ (rho ^ n / n) / (lambda ^ n / n) := hstep₂
      _ = (rho / lambda) ^ n := hratio

end Omega.DerivedConsequences
