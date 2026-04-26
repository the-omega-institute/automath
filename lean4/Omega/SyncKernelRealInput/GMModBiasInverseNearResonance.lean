import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Omega.SyncKernelRealInput

noncomputable section

/-- Finite-state bias data for the inverse near-resonance statement. The witness character is the
nontrivial Fourier mode extracted from the bias lower bound, and the decay parameter `τ` records
the twisted transfer-operator loss per step. -/
structure gm_mod_bias_inverse_near_resonance_data where
  q : ℕ
  m : ℕ
  δ : ℝ
  τ : ℝ
  witnessCharacter : ZMod q
  q_two_le : 2 ≤ q
  m_pos : 0 < m
  delta_pos : 0 < δ
  delta_le_one : δ ≤ 1
  tau_nonneg : 0 ≤ τ
  witnessCharacter_nontrivial : witnessCharacter ≠ 0
  bias_to_fourier :
    δ ≤ Real.exp (-((m : ℝ) * τ))

/-- The normalized nontrivial Fourier coefficient carried by the extracted character. -/
def gm_mod_bias_inverse_near_resonance_witnessCoeff
    (D : gm_mod_bias_inverse_near_resonance_data) : ℝ :=
  Real.exp (-((D.m : ℝ) * D.τ))

/-- The twisted-to-Perron spectral-radius ratio in the exponential model. -/
def gm_mod_bias_inverse_near_resonance_twistedRatio
    (D : gm_mod_bias_inverse_near_resonance_data) : ℝ :=
  Real.exp (-D.τ)

/-- Paper label: `prop:gm-mod-bias-inverse-near-resonance`. In the finite exponential model, a
modulus bias lower bound yields a nontrivial Fourier witness, and the same witness forces the
twisted spectral radius to stay within `log(1/δ)/m` of the Perron radius. -/
theorem paper_gm_mod_bias_inverse_near_resonance
    (D : gm_mod_bias_inverse_near_resonance_data) :
    ∃ χ : ZMod D.q,
      χ ≠ 0 ∧
        D.δ ≤ gm_mod_bias_inverse_near_resonance_witnessCoeff D ∧
        1 - Real.log (1 / D.δ) / (D.m : ℝ) ≤
          gm_mod_bias_inverse_near_resonance_twistedRatio D := by
  refine ⟨D.witnessCharacter, D.witnessCharacter_nontrivial, D.bias_to_fourier, ?_⟩
  have hm_pos : (0 : ℝ) < D.m := by exact_mod_cast D.m_pos
  have hdelta_inv_pos : 0 < 1 / D.δ := one_div_pos.mpr D.delta_pos
  have hlog : Real.log D.δ ≤ -((D.m : ℝ) * D.τ) := by
    have hlog_le :=
      Real.log_le_log D.delta_pos D.bias_to_fourier
    simpa [gm_mod_bias_inverse_near_resonance_witnessCoeff, Real.log_exp] using hlog_le
  have htau_le :
      D.τ ≤ Real.log (1 / D.δ) / (D.m : ℝ) := by
    have hneglog : (D.m : ℝ) * D.τ ≤ -Real.log D.δ := by
      linarith
    have hdiv : D.τ ≤ (-Real.log D.δ) / (D.m : ℝ) := by
      exact (le_div_iff₀ hm_pos).2 <| by simpa [mul_comm, mul_left_comm, mul_assoc] using hneglog
    simpa [one_div, Real.log_inv] using hdiv
  let x : ℝ := Real.log (1 / D.δ) / (D.m : ℝ)
  have hx_nonneg : 0 ≤ x := by
    have hlog_inv_nonneg : 0 ≤ Real.log (1 / D.δ) := by
      apply Real.log_nonneg
      exact one_le_one_div D.delta_pos D.delta_le_one
    exact div_nonneg hlog_inv_nonneg hm_pos.le
  have hlinexp : 1 - x ≤ Real.exp (-x) := Real.one_sub_le_exp_neg x
  have hexp_mono :
      Real.exp (-x) ≤ gm_mod_bias_inverse_near_resonance_twistedRatio D := by
    apply Real.exp_le_exp.mpr
    change -x ≤ -D.τ
    exact neg_le_neg htau_le
  have hfinal : 1 - x ≤ gm_mod_bias_inverse_near_resonance_twistedRatio D := by
    exact hlinexp.trans hexp_mono
  simpa [x, gm_mod_bias_inverse_near_resonance_twistedRatio] using hfinal
