import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic
import Omega.Zeta.HankelVandermonde2
import Omega.Zeta.XiPronyMomentMapJacobianDelta4

namespace Omega.Zeta

/-- Minimal-realization budget is controlled by the first Hankel determinant in the two-atom
Prony model. -/
def xiPomMinrealBudgetControlledByHankel (ω₁ ω₂ a₁ a₂ : ℤ) : Prop :=
  hankel2 ω₁ ω₂ a₁ a₂ = ω₁ * ω₂ * (a₂ - a₁) ^ 2

/-- Spectral recovery sees the Hankel budget together with an extra collision term coming from the
square of the Vandermonde gap. -/
def xiPomSpectralBudgetHasExtraCollisionTerm (p : ℕ) (ω₁ ω₂ a₁ a₂ : ℤ) : Prop :=
  padicValRat p ((pronyJacobian2 a₁ a₂ ω₁ ω₂).det : ℚ) =
    padicValRat p (hankel2 ω₁ ω₂ a₁ a₂ : ℚ) +
      (2 : ℤ) * padicValRat p ((a₂ - a₁ : ℤ) : ℚ)

/-- A positive collision valuation forces the spectral budget to be strictly larger than the
minimal Hankel budget. -/
def xiPomCollisionImpliesStrictSeparation (p : ℕ) (ω₁ ω₂ a₁ a₂ : ℤ) : Prop :=
  0 < padicValRat p ((a₂ - a₁ : ℤ) : ℚ) →
    padicValRat p (hankel2 ω₁ ω₂ a₁ a₂ : ℚ) <
      padicValRat p ((pronyJacobian2 a₁ a₂ ω₁ ω₂).det : ℚ)

private theorem xiPom_prony_det_eq_hankel_times_collision_sq
    (ω₁ ω₂ a₁ a₂ : ℤ) :
    (pronyJacobian2 a₁ a₂ ω₁ ω₂).det =
      -(hankel2 ω₁ ω₂ a₁ a₂) * (a₂ - a₁) ^ 2 := by
  rw [paper_xi_prony_moment_map_jacobian_delta4, hankel2_vandermonde_square]
  ring

/-- Paper-facing `κ = 2` budget separation: the Hankel determinant gives the minimal-realization
threshold, while the Prony Jacobian carries an additional doubled collision valuation; therefore
any positive collision valuation produces strict budget separation.
    cor:xi-pom-minreal-vs-spectral-budget-separation -/
theorem paper_xi_pom_minreal_vs_spectral_budget_separation
    (p : ℕ) (ω₁ ω₂ a₁ a₂ : ℤ) (hp : Nat.Prime p)
    (hH : hankel2 ω₁ ω₂ a₁ a₂ ≠ 0) :
    xiPomMinrealBudgetControlledByHankel ω₁ ω₂ a₁ a₂ ∧
      xiPomSpectralBudgetHasExtraCollisionTerm p ω₁ ω₂ a₁ a₂ ∧
      xiPomCollisionImpliesStrictSeparation p ω₁ ω₂ a₁ a₂ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hgap_int : a₂ - a₁ ≠ 0 := by
    intro hgap
    apply hH
    rw [hankel2_vandermonde_square, hgap]
    ring
  have hHq : (hankel2 ω₁ ω₂ a₁ a₂ : ℚ) ≠ 0 := by
    exact_mod_cast hH
  have hgap : ((a₂ - a₁ : ℤ) : ℚ) ≠ 0 := by
    exact_mod_cast hgap_int
  have hdetq :
      ((pronyJacobian2 a₁ a₂ ω₁ ω₂).det : ℚ) =
        -(hankel2 ω₁ ω₂ a₁ a₂ : ℚ) * (((a₂ - a₁ : ℤ) : ℚ) ^ 2) := by
    exact_mod_cast xiPom_prony_det_eq_hankel_times_collision_sq ω₁ ω₂ a₁ a₂
  have hspectral :
      xiPomSpectralBudgetHasExtraCollisionTerm p ω₁ ω₂ a₁ a₂ := by
    rw [xiPomSpectralBudgetHasExtraCollisionTerm]
    calc
      padicValRat p ((pronyJacobian2 a₁ a₂ ω₁ ω₂).det : ℚ)
          = padicValRat p (-(hankel2 ω₁ ω₂ a₁ a₂ : ℚ) * (((a₂ - a₁ : ℤ) : ℚ) ^ 2)) := by
              rw [hdetq]
      _ = padicValRat p (-(hankel2 ω₁ ω₂ a₁ a₂ : ℚ)) +
            padicValRat p ((((a₂ - a₁ : ℤ) : ℚ) ^ 2)) := by
              simpa using
                padicValRat.mul (p := p) (q := -(hankel2 ω₁ ω₂ a₁ a₂ : ℚ))
                  (r := (((a₂ - a₁ : ℤ) : ℚ) ^ 2)) (neg_ne_zero.mpr hHq) (pow_ne_zero 2 hgap)
      _ = padicValRat p (hankel2 ω₁ ω₂ a₁ a₂ : ℚ) +
            (2 : ℤ) * padicValRat p ((a₂ - a₁ : ℤ) : ℚ) := by
              rw [padicValRat.neg, padicValRat.pow hgap]
              norm_num
  refine ⟨hankel2_vandermonde_square ω₁ ω₂ a₁ a₂, hspectral, ?_⟩
  rw [xiPomCollisionImpliesStrictSeparation]
  intro hcollision
  rw [hspectral]
  linarith

end Omega.Zeta
