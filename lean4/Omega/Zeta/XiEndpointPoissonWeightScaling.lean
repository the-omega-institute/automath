import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Endpoint Poisson weight in the audited linearized model. -/
def endpointPoissonWeight (a : ℂ) : ℂ :=
  a

/-- The scale map `ψ_m` acting on the audited zero set. -/
def psiScale (m : ℕ) (a : ℂ) : ℂ :=
  (m : ℂ) * a

/-- Push a finite zero set forward by the scale map `ψ_m`. -/
noncomputable def pushZerosByPsi (m : ℕ) (zeros : Finset ℂ) : Finset ℂ :=
  zeros.image (psiScale m)

/-- Endpoint flux obtained by summing the single-zero Poisson weights. -/
noncomputable def endpointFlux (zeros : Finset ℂ) : ℂ :=
  Finset.sum zeros endpointPoissonWeight

private theorem psiScale_injective (m : ℕ) (hm : 1 < m) : Function.Injective (psiScale m) := by
  intro a b hab
  have hm0_nat : m ≠ 0 := by
    linarith
  have hm0 : (m : ℂ) ≠ 0 := by
    exact_mod_cast hm0_nat
  exact mul_left_cancel₀ hm0 hab

private theorem endpointPoissonWeight_psiScale (m : ℕ) (a : ℂ) :
    endpointPoissonWeight (psiScale m a) = (m : ℂ) * endpointPoissonWeight a := by
  rfl

/-- The endpoint Poisson weight scales linearly under the audited scale map `ψ_m`, and hence so
does the finite endpoint flux after pushing the zero set forward termwise.
    thm:xi-endpoint-poisson-weight-scaling -/
theorem paper_xi_endpoint_poisson_weight_scaling (m : ℕ) (hm : 1 < m) (zeros : Finset ℂ) :
    endpointFlux (pushZerosByPsi m zeros) = m * endpointFlux zeros := by
  unfold endpointFlux pushZerosByPsi
  calc
    Finset.sum (zeros.image (psiScale m)) endpointPoissonWeight
      = Finset.sum zeros (fun a => endpointPoissonWeight (psiScale m a)) := by
          refine Finset.sum_image ?_
          intro a ha b hb hab
          exact psiScale_injective m hm hab
    _ = Finset.sum zeros (fun a => (m : ℂ) * endpointPoissonWeight a) := by
          refine Finset.sum_congr rfl ?_
          intro a ha
          simp [endpointPoissonWeight_psiScale]
    _ = (m : ℂ) * Finset.sum zeros endpointPoissonWeight := by
          rw [Finset.mul_sum]
    _ = m * Finset.sum zeros endpointPoissonWeight := by norm_num

end Omega.Zeta
