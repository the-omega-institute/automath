import Mathlib
import Omega.Zeta.XiReverseKLSingleFrequencyRigidityEquivalences

namespace Omega.Conclusion

/-- Positive-frequency Fourier magnitudes of the single-frequency reverse-KL extremizer family. -/
noncomputable def reverseKLSingleFrequencyCoeff (n : ℕ) (c : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then 1 else if n ∣ k then c ^ (k / n) else 0

/-- Fourier magnitudes of Haar measure on the circle. -/
def reverseKLHaarCoeff (k : ℕ) : ℝ := if k = 0 then 1 else 0

private lemma reverseKLSingleFrequencyCoeff_zero_eq_haar (n : ℕ) (hn : 1 ≤ n) :
    reverseKLSingleFrequencyCoeff n 0 = reverseKLHaarCoeff := by
  funext k
  by_cases hk : k = 0
  · simp [reverseKLSingleFrequencyCoeff, reverseKLHaarCoeff, hk]
  · by_cases hdiv : n ∣ k
    · rcases hdiv with ⟨ℓ, rfl⟩
      have hn_pos : 0 < n := by omega
      have hℓ_ne : ℓ ≠ 0 := by
        intro hℓ
        apply hk
        simp [hℓ]
      simp [reverseKLSingleFrequencyCoeff, reverseKLHaarCoeff, hk, hℓ_ne, hn_pos]
    · simp [reverseKLSingleFrequencyCoeff, reverseKLHaarCoeff, hk, hdiv]

/-- Single-frequency exact saturation is exclusive: once the `n`-frequency extremizer profile
also saturates the reverse-KL envelope at a distinct positive frequency `m`, the parameter must
collapse to the Haar endpoint `c = 0`.
    thm:conclusion-reversekl-single-frequency-exclusivity -/
theorem paper_conclusion_reversekl_single_frequency_exclusivity
    (n m : ℕ) (r c : ℝ) (hn : 1 ≤ n) (hm : 1 ≤ m) (hmn : n ≠ m) (hr : 0 < r ∧ r < 1)
    (hc : 0 ≤ c ∧ c ≤ 1)
    (hsat :
      Omega.Zeta.xi_reversekl_single_frequency_inf n r c =
        Omega.Zeta.xi_reversekl_single_frequency_inf m r (reverseKLSingleFrequencyCoeff n c m)) :
    reverseKLSingleFrequencyCoeff n c = reverseKLHaarCoeff := by
  by_cases hc0 : c = 0
  · simpa [hc0] using reverseKLSingleFrequencyCoeff_zero_eq_haar n hn
  · have hc_pos : 0 < c := lt_of_le_of_ne hc.1 fun h => hc0 h.symm
    let x : ℝ := r ^ (2 * n) * c ^ 2
    have hrpow_pos : 0 < r ^ (2 * n) := pow_pos hr.1 _
    have hx_pos : 0 < x := by
      dsimp [x]
      positivity
    have hrpow_lt_one : r ^ (2 * n) < 1 := by
      apply pow_lt_one₀ hr.1.le hr.2
      omega
    have hc_sq_le_one : c ^ 2 ≤ 1 := by
      simpa using (pow_le_one₀ hc.1 hc.2 (n := 2))
    have hx_le : x ≤ r ^ (2 * n) := by
      dsimp [x]
      nlinarith
    have hx_lt_one : x < 1 := lt_of_le_of_lt hx_le hrpow_lt_one
    have hx_log_pos : 0 < 1 - x := by linarith
    by_cases hdiv : n ∣ m
    · rcases hdiv with ⟨ℓ, rfl⟩
      have hn_pos : 0 < n := by omega
      have hℓ_ne_zero : ℓ ≠ 0 := by
        intro hℓ
        subst hℓ
        omega
      have hℓ_ge_two : 2 ≤ ℓ := by
        have hℓ_ne_one : ℓ ≠ 1 := by
          intro hℓ
          apply hmn
          simp [hℓ]
        omega
      have hcoeff : reverseKLSingleFrequencyCoeff n c (n * ℓ) = c ^ ℓ := by
        have hnm_ne : n * ℓ ≠ 0 := by omega
        simp [reverseKLSingleFrequencyCoeff, hnm_ne, hn_pos]
      have hxpow :
          x ^ ℓ = r ^ (2 * (n * ℓ)) * (c ^ ℓ) ^ 2 := by
        dsimp [x]
        have hr_exp : (2 * n) * ℓ = 2 * (n * ℓ) := by rw [Nat.mul_assoc]
        have hc_exp : 2 * ℓ = ℓ * 2 := by rw [Nat.mul_comm]
        have hc_sq : c ^ (ℓ * 2) = (c ^ ℓ) ^ 2 := by rw [pow_mul]
        calc
          (r ^ (2 * n) * c ^ 2) ^ ℓ = (r ^ (2 * n)) ^ ℓ * (c ^ 2) ^ ℓ := by rw [mul_pow]
          _ = r ^ ((2 * n) * ℓ) * c ^ (2 * ℓ) := by rw [← pow_mul, ← pow_mul]
          _ = r ^ (2 * (n * ℓ)) * c ^ (2 * ℓ) := by rw [hr_exp]
          _ = r ^ (2 * (n * ℓ)) * c ^ (ℓ * 2) := by rw [hc_exp]
          _ = r ^ (2 * (n * ℓ)) * (c ^ ℓ) ^ 2 := by rw [hc_sq]
      have hsat' : -Real.log (1 - x) = -Real.log (1 - x ^ ℓ) := by
        have hsat'' := hsat
        rw [Omega.Zeta.xi_reversekl_single_frequency_inf,
          Omega.Zeta.xi_reversekl_single_frequency_inf, hcoeff, ← hxpow] at hsat''
        simpa [x] using hsat''
      have hxpow_lt_one : x ^ ℓ < 1 := pow_lt_one₀ hx_pos.le hx_lt_one hℓ_ne_zero
      have hxpow_log_pos : 0 < 1 - x ^ ℓ := by linarith
      have hlog_eq : Real.log (1 - x) = Real.log (1 - x ^ ℓ) := by linarith
      have hinside : 1 - x = 1 - x ^ ℓ := by
        exact Real.log_injOn_pos hx_log_pos hxpow_log_pos hlog_eq
      have hxeq : x = x ^ ℓ := by linarith
      have hxpow_succ_lt : x ^ ℓ < x := by
        have hxpow_pred_lt_one : x ^ (ℓ - 1) < 1 := by
          apply pow_lt_one₀ hx_pos.le hx_lt_one
          exact Nat.sub_ne_zero_of_lt (by omega)
        have hmul_lt : x ^ (ℓ - 1) * x < 1 * x := by
          exact mul_lt_mul_of_pos_right hxpow_pred_lt_one hx_pos
        have hxpow_aux : x ^ ((ℓ - 1) + 1) < x := by
          simpa [pow_succ, one_mul] using hmul_lt
        have hℓ_succ : ℓ = (ℓ - 1) + 1 := by omega
        rw [hℓ_succ]
        exact hxpow_aux
      have : False := (lt_irrefl x) <| calc
        x = x ^ ℓ := hxeq
        _ < x := hxpow_succ_lt
      exact False.elim this
    · have hsat' : -Real.log (1 - x) = 0 := by
        have hm_ne : m ≠ 0 := by omega
        have hsat'' := hsat
        rw [Omega.Zeta.xi_reversekl_single_frequency_inf,
          Omega.Zeta.xi_reversekl_single_frequency_inf] at hsat''
        simpa [reverseKLSingleFrequencyCoeff, hdiv, hm_ne, x] using hsat''
      have hlog_zero : Real.log (1 - x) = 0 := by linarith
      rcases (Real.log_eq_zero.mp hlog_zero) with hzero | hone | hneg
      · linarith
      · have : False := by linarith
        exact False.elim this
      · linarith

end Omega.Conclusion
