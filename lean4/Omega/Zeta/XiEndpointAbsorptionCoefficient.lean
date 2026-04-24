import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic
import Omega.Zeta.XiEndpointJuliaIndicatorEqualsAbsorption

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- The endpoint coefficient attached to a finite Blaschke family is the absorption profile with
unit Poisson weights. -/
def xiEndpointAbsorptionCoefficient {κ : Nat} (a : Fin κ → ℂ) : ℝ :=
  xiEndpointAbsorption (fun _ => 1) a

private lemma xiEndpointAbsorptionCoefficient_term_pos {z : ℂ} (hz : ‖z‖ < 1) :
    0 < (1 - ‖z‖ ^ 2) / ‖1 + z‖ ^ 2 := by
  have hnum : 0 < 1 - ‖z‖ ^ 2 := by
    have hsq : ‖z‖ ^ 2 < 1 := by
      nlinarith [norm_nonneg z, hz]
    linarith
  have hplus_ne : 1 + z ≠ 0 := by
    intro hz0
    have hz_eq : z = -1 := by
      have hneg : (-1 : ℂ) = z := by
        simpa using (neg_eq_iff_add_eq_zero.mpr hz0)
      exact hneg.symm
    have hnorm_one : ‖z‖ = 1 := by
      simpa [hz_eq]
    linarith
  have hden : 0 < ‖1 + z‖ ^ 2 := by
    exact pow_pos (norm_pos_iff.2 hplus_ne) 2
  exact div_pos hnum hden

private lemma xiEndpointAbsorptionCoefficient_pos_of_nonempty
    {κ : Nat} (a : Fin κ → ℂ) (hκ : 0 < κ) (ha : ∀ k, ‖a k‖ < 1) :
    0 < xiEndpointAbsorptionCoefficient a := by
  classical
  let f : Fin κ → ℝ := fun k => (1 - ‖a k‖ ^ 2) / ‖1 + a k‖ ^ 2
  have hsum : 0 < ∑ k : Fin κ, f k := by
    refine Finset.sum_pos' ?_ ?_
    · intro k hk
      exact le_of_lt (xiEndpointAbsorptionCoefficient_term_pos (ha k))
    · refine ⟨⟨0, hκ⟩, Finset.mem_univ _, xiEndpointAbsorptionCoefficient_term_pos (ha ⟨0, hκ⟩)⟩
  simpa [xiEndpointAbsorptionCoefficient, xiEndpointAbsorption, xiEndpointAbsorptionTerm, f] using
    hsum

/-- Paper label: `prop:xi-endpoint-absorption-coefficient`. -/
theorem paper_xi_endpoint_absorption_coefficient
    {κ : Nat} (a : Fin κ → ℂ) (ha : ∀ k, ‖a k‖ < 1) :
    (xiEndpointAbsorptionCoefficient a =
      ∑ k, (1 - ‖a k‖ ^ 2) / ‖1 + a k‖ ^ 2) ∧
      (xiEndpointAbsorptionCoefficient a = 0 ↔ κ = 0) := by
  constructor
  · simp [xiEndpointAbsorptionCoefficient, xiEndpointAbsorption, xiEndpointAbsorptionTerm]
  · constructor
    · intro hzero
      by_contra hκ
      have hpos : 0 < xiEndpointAbsorptionCoefficient a :=
        xiEndpointAbsorptionCoefficient_pos_of_nonempty a (Nat.pos_of_ne_zero hκ) ha
      linarith
    · intro hκ
      subst hκ
      simp [xiEndpointAbsorptionCoefficient, xiEndpointAbsorption]

end

end Omega.Zeta
