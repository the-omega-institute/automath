import Omega.Zeta.XiSatakeTraceEllipseTemperedSegment
import Omega.Zeta.XiSelfreciprocalEscapeJensen

namespace Omega.Zeta

noncomputable section

/-- The finite trace-root criterion and the self-reciprocal escape-zero criterion used for the
singular-ring resultant unit-circle test. -/
def xi_unit_circle_criterion_singular_ring_resultant_statement : Prop :=
  (∀ {n : ℕ} (traceRoot : Fin n → ℝ),
    (∀ j : Fin n, traceRoot j ∈ Set.Icc (-2 : ℝ) 2) ↔
      ∀ j : Fin n, ∃ α : ℂ,
        ‖α‖ = 1 ∧
          xi_satake_trace_ellipse_tempered_segment_trace α = (traceRoot j : ℂ)) ∧
    (∀ {n : ℕ} (radius : Fin n → ℝ) (jensenAverage leadingLogAbs : ℝ),
      (∀ j : Fin n, 0 < radius j) →
      xi_selfreciprocal_escape_jensen_rootPairing radius →
      xi_selfreciprocal_escape_jensen_pairedEscapeIdentity radius →
      xi_selfreciprocal_escape_jensen_averageFormula radius jensenAverage leadingLogAbs →
        (xi_selfreciprocal_escape_jensen_escape radius = 0 ↔
          ∀ j : Fin n, radius j = 1))

/-- Paper label: `cor:xi-unit-circle-criterion-singular-ring-resultant`. -/
theorem paper_xi_unit_circle_criterion_singular_ring_resultant :
    xi_unit_circle_criterion_singular_ring_resultant_statement := by
  refine ⟨?_, ?_⟩
  · intro n traceRoot
    constructor
    · intro hsegment j
      exact (paper_xi_satake_trace_ellipse_tempered_segment.2.2 (traceRoot j)).mp
        (hsegment j)
    · intro hpreimage j
      exact (paper_xi_satake_trace_ellipse_tempered_segment.2.2 (traceRoot j)).mpr
        (hpreimage j)
  · intro n radius jensenAverage leadingLogAbs hpositive hpair hpaired haverage
    exact
      (paper_xi_selfreciprocal_escape_jensen radius jensenAverage leadingLogAbs hpositive
        hpair hpaired haverage).2

end

end Omega.Zeta
