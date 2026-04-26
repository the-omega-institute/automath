import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete perturbative package for the singular spectrum of a Hankel block written as a rank-one
spike plus an entrywise-bounded error. The coarse operator bound `κ B` is recorded explicitly, and
the singular values are indexed in the usual `1,2,3,...` order. -/
structure XiHankelSpikeSingularSpectrumData where
  κ : ℕ
  u0 : ℝ
  B : ℝ
  errorOpNorm : ℝ
  singularValue : ℕ → ℝ
  hB_nonneg : 0 ≤ B
  herror_nonneg : 0 ≤ errorOpNorm
  error_operator_bound : errorOpNorm ≤ (κ : ℝ) * B
  spike_perturbation_lower : |u0| - errorOpNorm ≤ singularValue 1
  tail_perturbation_upper : ∀ j : ℕ, 2 ≤ j → singularValue j ≤ errorOpNorm

namespace XiHankelSpikeSingularSpectrumData

/-- The coarse Frobenius/operator estimate attached to the error term. -/
def errorControlled (D : XiHankelSpikeSingularSpectrumData) : Prop :=
  D.errorOpNorm ≤ (D.κ : ℝ) * D.B

/-- Singular-spectrum separation: the leading singular value stays within `κ B` of the spike size,
and every non-leading singular value is bounded by the same coarse envelope. -/
def singularSpectrumSeparated (D : XiHankelSpikeSingularSpectrumData) : Prop :=
  (|D.u0| - (D.κ : ℝ) * D.B ≤ D.singularValue 1) ∧
    ∀ j : ℕ, 2 ≤ j → D.singularValue j ≤ (D.κ : ℝ) * D.B

end XiHankelSpikeSingularSpectrumData

/-- Paper label: `thm:xi-hankel-spike-singular-spectrum-separation`. Bounding each error entry by
`B` yields the coarse operator estimate `‖E‖_op ≤ κ B`; singular-value perturbation then gives the
lower bound on `σ₁` and the uniform `κ B` upper bound on the tail singular values. -/
theorem paper_xi_hankel_spike_singular_spectrum_separation
    (D : XiHankelSpikeSingularSpectrumData) : D.singularSpectrumSeparated := by
  refine ⟨?_, ?_⟩
  · linarith [D.error_operator_bound, D.spike_perturbation_lower]
  · intro j hj
    exact le_trans (D.tail_perturbation_upper j hj) D.error_operator_bound

end Omega.Zeta
