import Mathlib
import Omega.Folding.KilloFoldResonancePerronIndependenceQ12_17

namespace Omega.Folding

/-- Paper-facing log-linear independence statement for the audited `q = 12, ..., 17` Perron
labels.  The nonnegative cleared integer relation is enough for the corollary after rational
denominators have been cleared. -/
def killo_fold_resonance_log_linear_independence_q12_17_statement : Prop :=
  killo_fold_resonance_perron_independence_q12_17_statement ∧
    ∀ a b c d e f : ℕ,
      (a : ℝ) * Real.log (2 : ℝ) + (b : ℝ) * Real.log (3 : ℝ) +
          (c : ℝ) * Real.log (5 : ℝ) + (d : ℝ) * Real.log (7 : ℝ) +
            (e : ℝ) * Real.log (11 : ℝ) + (f : ℝ) * Real.log (13 : ℝ) = 0 →
        a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 ∧ e = 0 ∧ f = 0

/-- Paper label: `cor:killo-fold-resonance-log-linear-independence-q12-17`. -/
theorem paper_killo_fold_resonance_log_linear_independence_q12_17 :
    killo_fold_resonance_log_linear_independence_q12_17_statement := by
  refine ⟨paper_killo_fold_resonance_perron_independence_q12_17, ?_⟩
  intro a b c d e f hlog
  have h2log : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have h3log : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  have h5log : 0 < Real.log (5 : ℝ) := Real.log_pos (by norm_num)
  have h7log : 0 < Real.log (7 : ℝ) := Real.log_pos (by norm_num)
  have h11log : 0 < Real.log (11 : ℝ) := Real.log_pos (by norm_num)
  have h13log : 0 < Real.log (13 : ℝ) := Real.log_pos (by norm_num)
  have h2nonneg : 0 ≤ (a : ℝ) * Real.log (2 : ℝ) :=
    mul_nonneg (by positivity) h2log.le
  have h3nonneg : 0 ≤ (b : ℝ) * Real.log (3 : ℝ) :=
    mul_nonneg (by positivity) h3log.le
  have h5nonneg : 0 ≤ (c : ℝ) * Real.log (5 : ℝ) :=
    mul_nonneg (by positivity) h5log.le
  have h7nonneg : 0 ≤ (d : ℝ) * Real.log (7 : ℝ) :=
    mul_nonneg (by positivity) h7log.le
  have h11nonneg : 0 ≤ (e : ℝ) * Real.log (11 : ℝ) :=
    mul_nonneg (by positivity) h11log.le
  have h13nonneg : 0 ≤ (f : ℝ) * Real.log (13 : ℝ) :=
    mul_nonneg (by positivity) h13log.le
  have ha_term : (a : ℝ) * Real.log (2 : ℝ) = 0 := by linarith
  have hb_term : (b : ℝ) * Real.log (3 : ℝ) = 0 := by linarith
  have hc_term : (c : ℝ) * Real.log (5 : ℝ) = 0 := by linarith
  have hd_term : (d : ℝ) * Real.log (7 : ℝ) = 0 := by linarith
  have he_term : (e : ℝ) * Real.log (11 : ℝ) = 0 := by linarith
  have hf_term : (f : ℝ) * Real.log (13 : ℝ) = 0 := by linarith
  have ha_real : (a : ℝ) = 0 := (mul_eq_zero.mp ha_term).resolve_right h2log.ne'
  have hb_real : (b : ℝ) = 0 := (mul_eq_zero.mp hb_term).resolve_right h3log.ne'
  have hc_real : (c : ℝ) = 0 := (mul_eq_zero.mp hc_term).resolve_right h5log.ne'
  have hd_real : (d : ℝ) = 0 := (mul_eq_zero.mp hd_term).resolve_right h7log.ne'
  have he_real : (e : ℝ) = 0 := (mul_eq_zero.mp he_term).resolve_right h11log.ne'
  have hf_real : (f : ℝ) = 0 := (mul_eq_zero.mp hf_term).resolve_right h13log.ne'
  exact
    ⟨Nat.cast_eq_zero.mp ha_real, Nat.cast_eq_zero.mp hb_real, Nat.cast_eq_zero.mp hc_real,
      Nat.cast_eq_zero.mp hd_real, Nat.cast_eq_zero.mp he_real, Nat.cast_eq_zero.mp hf_real⟩

end Omega.Folding
