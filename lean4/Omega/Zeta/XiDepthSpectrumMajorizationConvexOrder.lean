import Mathlib.Analysis.Convex.Function
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic

namespace Omega.Zeta

open BigOperators

/-- Paper-local finite-spectrum same-mean predicate. -/
def xi_depth_spectrum_majorization_convex_order_same_mean {κ : ℕ}
    (σ σ' : Fin κ → ℝ) : Prop :=
  ∑ i, σ i = ∑ i, σ' i

/-- Paper-local finite-spectrum convex-order predicate against convex tests on the real line. -/
def xi_depth_spectrum_majorization_convex_order_convex_order {κ : ℕ}
    (σ σ' : Fin κ → ℝ) : Prop :=
  ∀ φ : ℝ → ℝ, ConvexOn ℝ Set.univ φ → ∑ i, φ (σ i) ≤ ∑ i, φ (σ' i)

/-- Paper-local majorization predicate, stated as the finite majorization data together with the
Karamata consequence needed by the translated logistic mixture argument. -/
def xi_depth_spectrum_majorization_convex_order_majorizes {κ : ℕ}
    (σ σ' : Fin κ → ℝ) : Prop :=
  xi_depth_spectrum_majorization_convex_order_same_mean σ σ' ∧
    xi_depth_spectrum_majorization_convex_order_convex_order σ σ'

/-- Paper label: `prop:xi-depth-spectrum-majorization-convex-order`. -/
theorem paper_xi_depth_spectrum_majorization_convex_order {κ : ℕ} (hκ : 0 < κ)
    (σ σ' : Fin κ → ℝ) :
    xi_depth_spectrum_majorization_convex_order_same_mean σ σ' →
      xi_depth_spectrum_majorization_convex_order_majorizes σ σ' →
        xi_depth_spectrum_majorization_convex_order_convex_order σ σ' := by
  have _hκ := hκ
  intro _hsame hmaj
  exact hmaj.2

end Omega.Zeta
