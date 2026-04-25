import Mathlib.Tactic
import Omega.Zeta.ZeroDispersionIdentifiability

open scoped BigOperators

namespace Omega.Zeta

noncomputable section

/-- The second-order circle-dimension bookkeeping keeps only the support size. -/
def xi_second_order_circle_dimension_signature_completeness_cdim {n : ℕ}
    (_p : Fin (n + 1) → ℝ) : ℕ :=
  n + 1

/-- The `γ`-coordinates record the canonical zero-dispersion support. -/
def xi_second_order_circle_dimension_signature_completeness_gamma {n : ℕ}
    (_p : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  zeroDispersionAtom

/-- The second-order `b`-curve is the tail-slope profile. -/
def xi_second_order_circle_dimension_signature_completeness_b {n : ℕ}
    (p : Fin (n + 1) → ℝ) : ℝ → ℝ :=
  zeroDispersionQ p

/-- The paper-facing second-order signature `(cdim, γ, b)`. -/
def xi_second_order_circle_dimension_signature_completeness_signature {n : ℕ}
    (p : Fin (n + 1) → ℝ) : ℕ × (Fin (n + 1) → ℝ) × (ℝ → ℝ) :=
  (xi_second_order_circle_dimension_signature_completeness_cdim p,
    xi_second_order_circle_dimension_signature_completeness_gamma p,
    xi_second_order_circle_dimension_signature_completeness_b p)

/-- Statement package for the second-order circle-dimension signature completeness claim. -/
def xi_second_order_circle_dimension_signature_completeness_statement {n : ℕ}
    (p : Fin (n + 1) → ℝ) : Prop :=
  ((∀ i, 0 ≤ p i) ∧ ∑ i : Fin (n + 1), p i = 1) →
    zeroDispersionPhiRegularity p ∧
      zeroDispersionPhiDerivativeEqQ p ∧
      ∀ p' : Fin (n + 1) → ℝ,
        xi_second_order_circle_dimension_signature_completeness_signature p' =
            xi_second_order_circle_dimension_signature_completeness_signature p →
          p' = p

/-- Paper label: `prop:xi-second-order-circle-dimension-signature-completeness`. Packaging the
second-order signature as `(cdim, γ, b)`, the `b`-curve is exactly the zero-dispersion tail-slope
profile, so the existing identifiability theorem recovers the finite-atom law and the `cdim, γ`
fields are pure bookkeeping. -/
theorem paper_xi_second_order_circle_dimension_signature_completeness {n : ℕ}
    (p : Fin (n + 1) → ℝ) : xi_second_order_circle_dimension_signature_completeness_statement p := by
  rintro ⟨hp_nonneg, hp_sum⟩
  rcases paper_xi_zero_dispersion_identifiability p hp_nonneg hp_sum with ⟨hreg, hder, hrec⟩
  refine ⟨hreg, hder, ?_⟩
  intro p' hsig
  have hb :
      xi_second_order_circle_dimension_signature_completeness_b p' =
        xi_second_order_circle_dimension_signature_completeness_b p := by
    simpa [xi_second_order_circle_dimension_signature_completeness_signature] using
      congrArg Prod.snd (congrArg Prod.snd hsig)
  exact hrec p' fun t => by
    simpa [xi_second_order_circle_dimension_signature_completeness_b] using congrFun hb t

end

end Omega.Zeta
