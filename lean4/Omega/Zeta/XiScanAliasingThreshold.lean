import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open Complex

open scoped BigOperators

noncomputable section

/-- Finite sampled fingerprint for a height parameter `γ` on a scan grid of spacing `Δ`. The
summation variable is an integer sample index, so shifts by integer multiples of `2π / Δ` are
exact aliases. -/
def xi_scan_aliasing_threshold_fingerprint {m : ℕ}
    (Δ γ : ℝ) (coeff : Fin m → ℂ) : ℂ :=
  ∑ n : Fin m, coeff n * Complex.exp ((((γ * Δ * n) : ℝ) : ℂ) * Complex.I)

lemma xi_scan_aliasing_threshold_fingerprint_periodic {m : ℕ}
    (Δ : ℝ) (hΔ : Δ ≠ 0) (γ : ℝ) (k : ℕ) (coeff : Fin m → ℂ) :
    xi_scan_aliasing_threshold_fingerprint Δ (γ + 2 * Real.pi * k / Δ) coeff =
      xi_scan_aliasing_threshold_fingerprint Δ γ coeff := by
  unfold xi_scan_aliasing_threshold_fingerprint
  refine Finset.sum_congr rfl ?_
  intro n hn
  have hexp :
      Complex.exp ((((γ + 2 * Real.pi * k / Δ) * Δ * n : ℝ) : ℂ) * Complex.I) =
        Complex.exp ((((γ * Δ * n : ℝ) : ℂ) * Complex.I) + ((k * n : ℕ) : ℂ) * (2 * Real.pi * Complex.I)) := by
    congr 1
    norm_num
    field_simp [hΔ]
  rw [hexp, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I]
  simp [mul_assoc]

/-- Paper label: `prop:xi-scan-aliasing-threshold`. Integer-grid samples of a finite exponential
fingerprint are invariant under frequency shifts by integer multiples of `2π / Δ`. Consequently,
once `Δ ≥ π / T`, the band `[-T, T]` already contains the distinct aliased heights `±π / Δ`, so a
global no-aliasing principle on that interval necessarily forces `Δ < π / T`. -/
theorem paper_xi_scan_aliasing_threshold {m : ℕ}
    (Δ T : ℝ) (hΔ : 0 < Δ) (hT : 0 < T) (coeff : Fin m → ℂ) :
    (∀ γ : ℝ, ∀ k : ℕ,
      xi_scan_aliasing_threshold_fingerprint Δ (γ + 2 * Real.pi * k / Δ) coeff =
        xi_scan_aliasing_threshold_fingerprint Δ γ coeff) ∧
      ((Real.pi / T ≤ Δ) →
        ∃ γ₁ γ₂ : ℝ,
          γ₁ ∈ Set.Icc (-T) T ∧
            γ₂ ∈ Set.Icc (-T) T ∧
            γ₁ ≠ γ₂ ∧
            xi_scan_aliasing_threshold_fingerprint Δ γ₁ coeff =
              xi_scan_aliasing_threshold_fingerprint Δ γ₂ coeff) := by
  refine ⟨?_, ?_⟩
  · intro γ k
    exact xi_scan_aliasing_threshold_fingerprint_periodic Δ hΔ.ne' γ k coeff
  · intro hthreshold
    have hbound : Real.pi / Δ ≤ T := by
      apply (div_le_iff₀ hΔ).2
      have hmul' : Real.pi ≤ Δ * T := (div_le_iff₀ hT).mp hthreshold
      have hmul : Real.pi ≤ T * Δ := by simpa [mul_comm] using hmul'
      simpa [mul_comm] using hmul
    refine ⟨-(Real.pi / Δ), Real.pi / Δ, ?_, ?_, ?_, ?_⟩
    · constructor
      · exact neg_le_neg hbound
      · have hneg : -(Real.pi / Δ) ≤ 0 := by
          have hpi_pos : 0 < Real.pi / Δ := div_pos Real.pi_pos hΔ
          linarith
        exact hneg.trans hT.le
    · constructor
      · have hTneg : -T ≤ 0 := by linarith
        have hpi_nonneg : 0 ≤ Real.pi / Δ := by positivity
        exact hTneg.trans hpi_nonneg
      · exact hbound
    · have hpi_pos : 0 < Real.pi / Δ := div_pos Real.pi_pos hΔ
      linarith
    · have halias :=
        xi_scan_aliasing_threshold_fingerprint_periodic Δ hΔ.ne' (-(Real.pi / Δ)) 1 coeff
      have hshift : -(Real.pi / Δ) + 2 * Real.pi / Δ = Real.pi / Δ := by
        field_simp [hΔ.ne']
        ring
      have :
          xi_scan_aliasing_threshold_fingerprint Δ (Real.pi / Δ) coeff =
            xi_scan_aliasing_threshold_fingerprint Δ (-(Real.pi / Δ)) coeff := by
        simpa [hshift] using halias
      exact this.symm

end

end Omega.Zeta
