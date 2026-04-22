import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Zeta.XiTimePart9wBasicRootUnityErrorExponentToOne

open Filter Topology
open scoped goldenRatio

namespace Omega.Conclusion

/-- The Perron logarithmic scale `log λ` with `λ = φ²`. -/
noncomputable def conclusion_realinput40_oddprime_quadratic_near_perron_log_lambda : ℝ :=
  Real.log (Real.goldenRatio ^ (2 : ℕ))

/-- The quadratic coefficient `κ` in the odd-prime near-Perron model. -/
noncomputable def conclusion_realinput40_oddprime_quadratic_near_perron_kappa : ℝ :=
  (Real.pi ^ 2) * (8955 - 3983 * Real.sqrt 5) /
    (500 * conclusion_realinput40_oddprime_quadratic_near_perron_log_lambda)

/-- The quartic correction coefficient in the same model. -/
noncomputable def conclusion_realinput40_oddprime_quadratic_near_perron_quartic : ℝ :=
  (Real.pi ^ 4) * (1354428303 - 605718497 * Real.sqrt 5) /
    (150000 * conclusion_realinput40_oddprime_quadratic_near_perron_log_lambda)

/-- Concrete odd-prime near-Perron exponent model. -/
noncomputable def conclusion_realinput40_oddprime_quadratic_near_perron_beta (p : ℕ) : ℝ :=
  1 - conclusion_realinput40_oddprime_quadratic_near_perron_kappa / (p : ℝ) ^ 2 +
    conclusion_realinput40_oddprime_quadratic_near_perron_quartic / (p : ℝ) ^ 4

/-- Concrete conclusion package for the odd-prime near-Perron law: the coefficient `κ` has the
paper's closed form, it is positive, the `βₚ` model is explicitly quadratic-plus-quartic, it
tends to `1`, and it is eventually above `1/2` on odd primes. -/
def conclusion_realinput40_oddprime_quadratic_near_perron_statement : Prop :=
  conclusion_realinput40_oddprime_quadratic_near_perron_kappa =
      (Real.pi ^ 2) * (8955 - 3983 * Real.sqrt 5) /
        (500 * conclusion_realinput40_oddprime_quadratic_near_perron_log_lambda) ∧
    0 < conclusion_realinput40_oddprime_quadratic_near_perron_kappa ∧
    (∀ p : ℕ, Nat.Prime p → p ≠ 2 →
      conclusion_realinput40_oddprime_quadratic_near_perron_beta p =
        1 - conclusion_realinput40_oddprime_quadratic_near_perron_kappa / (p : ℝ) ^ 2 +
          conclusion_realinput40_oddprime_quadratic_near_perron_quartic / (p : ℝ) ^ 4) ∧
    Tendsto conclusion_realinput40_oddprime_quadratic_near_perron_beta atTop (𝓝 1) ∧
    ∃ N : ℕ, ∀ p : ℕ, Nat.Prime p → N ≤ p →
      1 / 2 < conclusion_realinput40_oddprime_quadratic_near_perron_beta p

lemma conclusion_realinput40_oddprime_quadratic_near_perron_sqrt5_lt :
    Real.sqrt 5 < (449 / 200 : ℝ) := by
  have hsqrt_nonneg : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have hsq :
      (Real.sqrt 5 : ℝ) ^ 2 < (449 / 200 : ℝ) ^ 2 := by
    have hsqrt_sq : (Real.sqrt 5 : ℝ) ^ 2 = 5 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by positivity)]
    have hbound_sq : (5 : ℝ) < (449 / 200 : ℝ) ^ 2 := by norm_num
    nlinarith
  have hbound_nonneg : (0 : ℝ) ≤ 449 / 200 := by positivity
  nlinarith

lemma conclusion_realinput40_oddprime_quadratic_near_perron_kappa_pos :
    0 < conclusion_realinput40_oddprime_quadratic_near_perron_kappa := by
  have hnum : 0 < 8955 - 3983 * Real.sqrt 5 := by
    have hsqrt5_lt : Real.sqrt 5 < (449 / 200 : ℝ) :=
      conclusion_realinput40_oddprime_quadratic_near_perron_sqrt5_lt
    nlinarith
  have hphi_sq_gt : 1 < Real.goldenRatio ^ (2 : ℕ) := by
    rw [show Real.goldenRatio ^ (2 : ℕ) = Real.goldenRatio + 1 by simpa using Real.goldenRatio_sq]
    linarith [Real.one_lt_goldenRatio]
  have hlog_pos :
      0 < conclusion_realinput40_oddprime_quadratic_near_perron_log_lambda := by
    unfold conclusion_realinput40_oddprime_quadratic_near_perron_log_lambda
    exact Real.log_pos hphi_sq_gt
  unfold conclusion_realinput40_oddprime_quadratic_near_perron_kappa
  refine div_pos ?_ ?_
  · exact mul_pos (by positivity) hnum
  · positivity

lemma conclusion_realinput40_oddprime_quadratic_near_perron_beta_tendsto :
    Tendsto conclusion_realinput40_oddprime_quadratic_near_perron_beta atTop (𝓝 1) := by
  have hpow2Real : Tendsto (fun t : ℝ => t ^ 2) atTop atTop := by
    exact tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)
  have hpow4Real : Tendsto (fun t : ℝ => t ^ 4) atTop atTop := by
    exact tendsto_pow_atTop (by norm_num : (4 : ℕ) ≠ 0)
  have hcast : Tendsto (fun p : ℕ => (p : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hpow2 : Tendsto (fun p : ℕ => (p : ℝ) ^ 2) atTop atTop := hpow2Real.comp hcast
  have hpow4 : Tendsto (fun p : ℕ => (p : ℝ) ^ 4) atTop atTop := hpow4Real.comp hcast
  have hinv2 : Tendsto (fun p : ℕ => ((p : ℝ) ^ 2)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hpow2
  have hinv4 : Tendsto (fun p : ℕ => ((p : ℝ) ^ 4)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hpow4
  have hterm2 :
      Tendsto
        (fun p : ℕ =>
          conclusion_realinput40_oddprime_quadratic_near_perron_kappa / (p : ℝ) ^ 2)
        atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds.mul hinv2)
  have hterm4 :
      Tendsto
        (fun p : ℕ =>
          conclusion_realinput40_oddprime_quadratic_near_perron_quartic / (p : ℝ) ^ 4)
        atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds.mul hinv4)
  have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hsub :
      Tendsto
        (fun p : ℕ =>
          1 - conclusion_realinput40_oddprime_quadratic_near_perron_kappa / (p : ℝ) ^ 2)
        atTop (𝓝 1) := by
    simpa using hconst.sub hterm2
  have hadd :
      Tendsto
        (fun p : ℕ =>
          (1 - conclusion_realinput40_oddprime_quadratic_near_perron_kappa / (p : ℝ) ^ 2) +
            conclusion_realinput40_oddprime_quadratic_near_perron_quartic / (p : ℝ) ^ 4)
        atTop (𝓝 (1 + 0)) :=
    hsub.add hterm4
  simpa [conclusion_realinput40_oddprime_quadratic_near_perron_beta] using hadd

/-- Paper label: `thm:conclusion-realinput40-oddprime-quadratic-near-perron`. -/
theorem paper_conclusion_realinput40_oddprime_quadratic_near_perron :
    conclusion_realinput40_oddprime_quadratic_near_perron_statement := by
  rcases Omega.Zeta.paper_xi_time_part9w_basic_root_unity_error_exponent_to_one with
    ⟨hAout, hBout, _⟩
  have hbeta_tendsto :
      Tendsto conclusion_realinput40_oddprime_quadratic_near_perron_beta atTop (𝓝 1) :=
    conclusion_realinput40_oddprime_quadratic_near_perron_beta_tendsto
  have hgt_eventually :
      ∀ᶠ p : ℕ in atTop, 1 / 2 <
        conclusion_realinput40_oddprime_quadratic_near_perron_beta p := by
    have hnhds : Set.Ioi (1 / 2 : ℝ) ∈ 𝓝 (1 : ℝ) := Ioi_mem_nhds (by norm_num)
    exact hbeta_tendsto.eventually hnhds
  rcases Filter.eventually_atTop.1 hgt_eventually with ⟨N, hN⟩
  refine ⟨?_, conclusion_realinput40_oddprime_quadratic_near_perron_kappa_pos, ?_,
    hbeta_tendsto, ⟨N, ?_⟩⟩
  · simpa [conclusion_realinput40_oddprime_quadratic_near_perron_kappa,
      conclusion_realinput40_oddprime_quadratic_near_perron_log_lambda] using hAout
  · intro p _hp _hodd
    rfl
  · intro p _hp hNp
    exact hN p hNp

end Omega.Conclusion
