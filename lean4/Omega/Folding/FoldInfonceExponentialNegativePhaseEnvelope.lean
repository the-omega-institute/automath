import Mathlib
import Omega.Folding.FoldInfonceRenyiCollisionUpperEnvelope

open Filter
open scoped Topology

namespace Omega.Folding

noncomputable section

/-- The affine envelope line indexed by the Rényi order `q`. -/
def fold_infonce_exponential_negative_phase_envelope_line
    (γ : ℝ) (h : ℕ → ℝ) (q : ℕ) : ℝ :=
  max (γ - h q / (q - 1 : ℝ)) 0

/-- Paper label: `cor:fold-infonce-exponential-negative-phase-envelope`.
Once each Rényi order `q ≥ 2` supplies a limsup upper bound by its affine envelope line, the
asymptotic loss is therefore bounded by every member of the corresponding piecewise-linear
envelope family. -/
theorem paper_fold_infonce_exponential_negative_phase_envelope
    (loss : ℕ → ℝ) (γ : ℝ) (h : ℕ → ℝ)
    (hbound :
      ∀ q : ℕ, 2 ≤ q →
        (limsup loss atTop : ℝ) ≤ fold_infonce_exponential_negative_phase_envelope_line γ h q) :
    ∀ q : {q : ℕ // 2 ≤ q},
      (limsup loss atTop : ℝ) ≤ fold_infonce_exponential_negative_phase_envelope_line γ h q.1 := by
  intro q
  exact hbound q.1 q.2

end

end Omega.Folding
