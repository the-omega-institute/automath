import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

attribute [local instance] Classical.decEq Classical.propDecidable

/-- Conditional uniformization on a finite visible fiber: sitewise invariance makes the
conditional mass constant on the visible fiber, the support hypothesis removes all off-fiber mass,
and normalization identifies the constant as the reciprocal fiber cardinal.
    thm:xi-time-part9z-window6-canonical-lift-conditional-uniformization -/
theorem paper_xi_time_part9z_window6_canonical_lift_conditional_uniformization
    {Λ Ω X : Type} [Fintype Λ] [Fintype Ω] [DecidableEq Ω] [DecidableEq X]
    (π : Ω → X) (w : Λ → X) (cond : (Λ → Ω) → ℝ)
    (hconst : ∀ ω ω', (∀ x, π (ω x) = w x) → (∀ x, π (ω' x) = w x) →
      cond ω = cond ω')
    (hsupport : ∀ ω, ¬ (∀ x, π (ω x) = w x) → cond ω = 0)
    (hsum : (∑ ω, cond ω) = 1) :
    ∀ ω, cond ω =
      if _ : ∀ x, π (ω x) = w x then
        ((Fintype.card {ω' : Λ → Ω // ∀ x, π (ω' x) = w x}) : ℝ)⁻¹
      else 0 := by
  classical
  intro ω
  by_cases hω : ∀ x, π (ω x) = w x
  · simp [hω]
    let P : (Λ → Ω) → Prop := fun η => ∀ x, π (η x) = w x
    let F : Type := {η : Λ → Ω // P η}
    let c : ℝ := cond ω
    have hcond_eq : ∀ η : Λ → Ω, cond η = if P η then c else 0 := by
      intro η
      by_cases hη : P η
      · simp [hη, c, P, hconst η ω hη hω]
      · simp [hη, hsupport η hη]
    have hsum_all :
        (∑ η : Λ → Ω, cond η) = ∑ η : Λ → Ω, if P η then c else 0 := by
      refine Finset.sum_congr rfl ?_
      intro η _
      exact hcond_eq η
    have hsum_if :
        (∑ η : Λ → Ω, if P η then c else 0) = (Fintype.card F : ℝ) * c := by
      calc
        (∑ η : Λ → Ω, if P η then c else 0)
            = (Finset.univ.filter P).sum (fun _ => c) := by
                exact (Finset.sum_filter (s := Finset.univ) (p := P) (f := fun _ => c)).symm
        _ = (Fintype.card F : ℝ) * c := by
                simp [F, P, Fintype.card_subtype, Finset.sum_const, nsmul_eq_mul, mul_comm]
    have hnorm : (Fintype.card F : ℝ) * c = 1 := by
      calc
        (Fintype.card F : ℝ) * c = (∑ η : Λ → Ω, if P η then c else 0) := hsum_if.symm
        _ = (∑ η : Λ → Ω, cond η) := hsum_all.symm
        _ = 1 := hsum
    have hc : c = ((Fintype.card F : ℝ))⁻¹ :=
      eq_inv_of_mul_eq_one_right hnorm
    simpa [F, P, c] using hc
  · simp [hω, hsupport ω hω]

end

end Omega.Zeta
