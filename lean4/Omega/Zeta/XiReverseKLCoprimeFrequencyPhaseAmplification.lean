import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

namespace Omega.Zeta

/-- The phase-error bound propagated by Bézout coefficients. -/
noncomputable def xi_reversekl_coprime_frequency_phase_amplification_phaseBound
    (u v epsilonP epsilonQ : ℝ) : ℝ :=
  (|u| * Real.sqrt epsilonP + |v| * Real.sqrt epsilonQ) ^ 2

/-- Paper label: `prop:xi-reversekl-coprime-frequency-phase-amplification`.

Once two coprime-frequency phase errors are controlled by Bézout coefficients, the first
frequency defect is bounded by the squared combined phase error, and that combined error is
bounded by `(p + q)^2` times the larger frequency defect. -/
theorem paper_xi_reversekl_coprime_frequency_phase_amplification
    (p q : ℕ) (u v : ℤ) (epsilonP epsilonQ defect : ℝ)
    (hBezout : u * (p : ℤ) + v * (q : ℤ) = 1)
    (hepsilonP : 0 ≤ epsilonP) (hepsilonQ : 0 ≤ epsilonQ)
    (hu_bound : |(u : ℝ)| ≤ (q : ℝ)) (hv_bound : |(v : ℝ)| ≤ (p : ℝ))
    (hPhase :
      defect ≤
        xi_reversekl_coprime_frequency_phase_amplification_phaseBound
          (u : ℝ) (v : ℝ) epsilonP epsilonQ) :
    u * (p : ℤ) + v * (q : ℤ) = 1 ∧
      defect ≤
        xi_reversekl_coprime_frequency_phase_amplification_phaseBound
          (u : ℝ) (v : ℝ) epsilonP epsilonQ ∧
      xi_reversekl_coprime_frequency_phase_amplification_phaseBound
          (u : ℝ) (v : ℝ) epsilonP epsilonQ ≤
        ((p : ℝ) + (q : ℝ)) ^ 2 * max epsilonP epsilonQ := by
  refine ⟨hBezout, hPhase, ?_⟩
  let M : ℝ := max epsilonP epsilonQ
  have hM_nonneg : 0 ≤ M := by
    by_cases h : epsilonP ≤ epsilonQ
    · simpa [M, max_eq_right h] using hepsilonQ
    · have hQP : epsilonQ ≤ epsilonP := le_of_not_ge h
      simpa [M, max_eq_left hQP] using hepsilonP
  have hsqrtP_le : Real.sqrt epsilonP ≤ Real.sqrt M :=
    Real.sqrt_le_sqrt (le_max_left epsilonP epsilonQ)
  have hsqrtQ_le : Real.sqrt epsilonQ ≤ Real.sqrt M :=
    Real.sqrt_le_sqrt (le_max_right epsilonP epsilonQ)
  have hu_nonneg : 0 ≤ |(u : ℝ)| := abs_nonneg _
  have hv_nonneg : 0 ≤ |(v : ℝ)| := abs_nonneg _
  have hsqrtM_nonneg : 0 ≤ Real.sqrt M := Real.sqrt_nonneg M
  have hP :
      |(u : ℝ)| * Real.sqrt epsilonP ≤ (q : ℝ) * Real.sqrt M :=
    mul_le_mul hu_bound hsqrtP_le (Real.sqrt_nonneg epsilonP) (Nat.cast_nonneg q)
  have hQ :
      |(v : ℝ)| * Real.sqrt epsilonQ ≤ (p : ℝ) * Real.sqrt M :=
    mul_le_mul hv_bound hsqrtQ_le (Real.sqrt_nonneg epsilonQ) (Nat.cast_nonneg p)
  have hLeft_nonneg :
      0 ≤ |(u : ℝ)| * Real.sqrt epsilonP + |(v : ℝ)| * Real.sqrt epsilonQ := by
    positivity
  have hRight_nonneg : 0 ≤ ((p : ℝ) + (q : ℝ)) * Real.sqrt M := by
    positivity
  have hLinear :
      |(u : ℝ)| * Real.sqrt epsilonP + |(v : ℝ)| * Real.sqrt epsilonQ ≤
        ((p : ℝ) + (q : ℝ)) * Real.sqrt M := by
    nlinarith
  have hSquare :
      (|((u : ℝ))| * Real.sqrt epsilonP + |((v : ℝ))| * Real.sqrt epsilonQ) ^ 2 ≤
        (((p : ℝ) + (q : ℝ)) * Real.sqrt M) ^ 2 := by
    nlinarith
  dsimp [xi_reversekl_coprime_frequency_phase_amplification_phaseBound]
  calc
    (|((u : ℝ))| * Real.sqrt epsilonP + |((v : ℝ))| * Real.sqrt epsilonQ) ^ 2
        ≤ (((p : ℝ) + (q : ℝ)) * Real.sqrt M) ^ 2 := hSquare
    _ = ((p : ℝ) + (q : ℝ)) ^ 2 * max epsilonP epsilonQ := by
      rw [mul_pow, Real.sq_sqrt hM_nonneg]

end Omega.Zeta
