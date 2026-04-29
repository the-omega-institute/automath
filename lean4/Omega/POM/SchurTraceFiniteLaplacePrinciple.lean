import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace Omega.POM

noncomputable section

/-- Concrete finite-layer data for the Schur trace Laplace principle.  The trace is the sum of an
effective layer and a certified remainder; when the effective coefficient cancels, a separate
finite-layer cancellation certificate gives the dropped exponent. -/
structure pom_schur_trace_finite_laplace_principle_data where
  pom_schur_trace_finite_laplace_principle_pressure : ℝ
  pom_schur_trace_finite_laplace_principle_topCoefficient : ℝ
  pom_schur_trace_finite_laplace_principle_errorGap : ℝ
  pom_schur_trace_finite_laplace_principle_cancellationGap : ℝ
  pom_schur_trace_finite_laplace_principle_remainder : ℕ → ℝ
  pom_schur_trace_finite_laplace_principle_errorGap_pos :
    0 < pom_schur_trace_finite_laplace_principle_errorGap
  pom_schur_trace_finite_laplace_principle_cancellationGap_pos :
    0 < pom_schur_trace_finite_laplace_principle_cancellationGap
  pom_schur_trace_finite_laplace_principle_remainder_bound :
    ∀ m : ℕ,
      |pom_schur_trace_finite_laplace_principle_remainder m| ≤
        Real.exp
          ((m : ℝ) *
            (pom_schur_trace_finite_laplace_principle_pressure -
              pom_schur_trace_finite_laplace_principle_errorGap))
  pom_schur_trace_finite_laplace_principle_cancellation_bound :
    ∀ m : ℕ,
      pom_schur_trace_finite_laplace_principle_topCoefficient = 0 →
        |pom_schur_trace_finite_laplace_principle_remainder m| ≤
          Real.exp
            ((m : ℝ) *
              (pom_schur_trace_finite_laplace_principle_pressure -
                pom_schur_trace_finite_laplace_principle_cancellationGap))

namespace pom_schur_trace_finite_laplace_principle_data

/-- The finite Schur trace reconstructed from its effective layer and certified finite remainder. -/
def pom_schur_trace_finite_laplace_principle_trace
    (D : pom_schur_trace_finite_laplace_principle_data) (m : ℕ) : ℝ :=
  D.pom_schur_trace_finite_laplace_principle_topCoefficient *
      Real.exp ((m : ℝ) * D.pom_schur_trace_finite_laplace_principle_pressure) +
    D.pom_schur_trace_finite_laplace_principle_remainder m

/-- Paper-facing dichotomy: a nonzero maximal coefficient yields a leading term with an exponential
gap, while total cancellation at that layer leaves only the certified lower exponent. -/
def finite_laplace_principle (D : pom_schur_trace_finite_laplace_principle_data) : Prop :=
  (D.pom_schur_trace_finite_laplace_principle_topCoefficient ≠ 0 →
    ∃ ε : ℝ,
      0 < ε ∧
        ∀ m : ℕ,
          D.pom_schur_trace_finite_laplace_principle_trace m =
              D.pom_schur_trace_finite_laplace_principle_topCoefficient *
                Real.exp
                  ((m : ℝ) * D.pom_schur_trace_finite_laplace_principle_pressure) +
                D.pom_schur_trace_finite_laplace_principle_remainder m ∧
            |D.pom_schur_trace_finite_laplace_principle_remainder m| ≤
              Real.exp
                ((m : ℝ) *
                  (D.pom_schur_trace_finite_laplace_principle_pressure - ε))) ∧
    (D.pom_schur_trace_finite_laplace_principle_topCoefficient = 0 →
      ∃ ε : ℝ,
        0 < ε ∧
          ∀ m : ℕ,
            |D.pom_schur_trace_finite_laplace_principle_trace m| ≤
              Real.exp
                ((m : ℝ) *
                  (D.pom_schur_trace_finite_laplace_principle_pressure - ε)))

end pom_schur_trace_finite_laplace_principle_data

open pom_schur_trace_finite_laplace_principle_data

/-- Paper label: `thm:pom-schur-trace-finite-laplace-principle`. -/
theorem paper_pom_schur_trace_finite_laplace_principle
    (D : pom_schur_trace_finite_laplace_principle_data) : D.finite_laplace_principle := by
  refine ⟨?_, ?_⟩
  · intro _hTop
    refine ⟨D.pom_schur_trace_finite_laplace_principle_errorGap,
      D.pom_schur_trace_finite_laplace_principle_errorGap_pos, ?_⟩
    intro m
    exact ⟨rfl, D.pom_schur_trace_finite_laplace_principle_remainder_bound m⟩
  · intro hCancel
    refine ⟨D.pom_schur_trace_finite_laplace_principle_cancellationGap,
      D.pom_schur_trace_finite_laplace_principle_cancellationGap_pos, ?_⟩
    intro m
    simpa [pom_schur_trace_finite_laplace_principle_trace, hCancel] using
      D.pom_schur_trace_finite_laplace_principle_cancellation_bound m hCancel

end

end Omega.POM
