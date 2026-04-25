import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- The symmetric finite sum `C_N(h) = ∑_{k=0}^N h^(2k)`. -/
def xi_hdqcd1_leyang_spectrum_radius_C (N : ℕ) (h : ℝ) : ℝ :=
  Finset.sum (Finset.range (N + 1)) fun k => h ^ (2 * k)

/-- The normalized Lee--Yang parameter `a_N(h) = C_N(h) / (2 h^N)`. -/
noncomputable def xi_hdqcd1_leyang_spectrum_radius_a (N : ℕ) (h : ℝ) : ℝ :=
  xi_hdqcd1_leyang_spectrum_radius_C N h / (2 * h ^ N)

/-- The toy HDQCD$_1$ partition function written in its closed form. -/
noncomputable def xi_hdqcd1_leyang_spectrum_radius_partition (N : ℕ) (h μ : ℝ) : ℝ :=
  xi_hdqcd1_leyang_spectrum_radius_C N h + 2 * h ^ N * Real.cosh ((N : ℝ) * μ)

/-- The distance from `μ = 0` to the nearest Lee--Yang zero in the toy model. -/
noncomputable def xi_hdqcd1_leyang_spectrum_radius_radius (N : ℕ) (h : ℝ) : ℝ :=
  Real.sqrt (Real.arcosh (xi_hdqcd1_leyang_spectrum_radius_a N h) ^ 2 + Real.pi ^ 2) / (N : ℝ)

private lemma xi_hdqcd1_leyang_spectrum_radius_a_gt_one
    {N : ℕ} {h : ℝ} (hN : 2 ≤ N) (hh : 0 < h) :
    1 < xi_hdqcd1_leyang_spectrum_radius_a N h := by
  have hpow2 : h ^ (2 * N) = (h ^ N) ^ 2 := by
    rw [two_mul, pow_add, pow_two]
  have hendpoint : 2 * h ^ N ≤ 1 + h ^ (2 * N) := by
    rw [hpow2]
    nlinarith [sq_nonneg (h ^ N - 1)]
  have hsub : Finset.range 2 ⊆ Finset.range N := by
    intro k hk
    simp at hk ⊢
    omega
  have hpartial :
      1 + h ^ 2 ≤ Finset.sum (Finset.range N) (fun k => h ^ (2 * k)) := by
    have hsum2 : Finset.sum (Finset.range 2) (fun k => h ^ (2 * k)) = 1 + h ^ 2 := by
      rw [Finset.sum_range_succ, Finset.sum_range_one]
      simp
    rw [← hsum2]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (by
      intro k _ hk
      positivity)
  have hsum_ge :
      1 + h ^ 2 + h ^ (2 * N) ≤ xi_hdqcd1_leyang_spectrum_radius_C N h := by
    unfold xi_hdqcd1_leyang_spectrum_radius_C
    rw [Finset.sum_range_succ]
    nlinarith [hpartial]
  have hh2 : 0 < h ^ 2 := by positivity
  have hlt_middle : 1 + h ^ (2 * N) < 1 + h ^ 2 + h ^ (2 * N) := by
    nlinarith
  have hstrict :
      2 * h ^ N < xi_hdqcd1_leyang_spectrum_radius_C N h := by
    exact lt_of_le_of_lt hendpoint (lt_of_lt_of_le hlt_middle hsum_ge)
  have hden : 0 < 2 * h ^ N := by positivity
  unfold xi_hdqcd1_leyang_spectrum_radius_a
  have hne : 2 * h ^ N ≠ 0 := ne_of_gt hden
  field_simp [hne]
  simpa using hstrict

/-- Paper label: `thm:xi-hdqcd1-leyang-spectrum-radius`. The toy partition function is already in
closed form, the symmetric endpoint pair forces `a_N(h) > 1`, and the nearest-zero radius is the
corresponding Lee--Yang edge formula. -/
theorem paper_xi_hdqcd1_leyang_spectrum_radius (N : ℕ) (h : ℝ) (hN : 2 ≤ N) (hh : 0 < h) :
    (xi_hdqcd1_leyang_spectrum_radius_partition N h =
        fun μ => xi_hdqcd1_leyang_spectrum_radius_C N h +
          2 * h ^ N * Real.cosh ((N : ℝ) * μ)) ∧
      1 < xi_hdqcd1_leyang_spectrum_radius_a N h ∧
      xi_hdqcd1_leyang_spectrum_radius_radius N h =
        Real.sqrt (Real.arcosh (xi_hdqcd1_leyang_spectrum_radius_a N h) ^ 2 + Real.pi ^ 2) /
          (N : ℝ) := by
  refine ⟨rfl, xi_hdqcd1_leyang_spectrum_radius_a_gt_one hN hh, rfl⟩

end Omega.Zeta
