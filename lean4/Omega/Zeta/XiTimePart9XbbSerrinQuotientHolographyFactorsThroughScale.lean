import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label:
`thm:xi-time-part9xbb-serrin-quotient-holography-factors-through-scale`. -/
theorem paper_xi_time_part9xbb_serrin_quotient_holography_factors_through_scale {A Z : Type*}
    (sigma : A → ℝ) (I : A → Z) (hsigma : Function.Injective sigma) :
    ∃! theta : Set.range sigma → Z, ∀ a : A, theta ⟨sigma a, ⟨a, rfl⟩⟩ = I a := by
  classical
  let theta : Set.range sigma → Z := fun x => I x.2.choose
  refine ⟨theta, ?_, ?_⟩
  · intro a
    dsimp [theta]
    have hchosen :
        sigma (Classical.choose (show ∃ b : A, sigma b = sigma a from ⟨a, rfl⟩)) =
          sigma a :=
      Classical.choose_spec (show ∃ b : A, sigma b = sigma a from ⟨a, rfl⟩)
    have hsame :
        Classical.choose (show ∃ b : A, sigma b = sigma a from ⟨a, rfl⟩) = a :=
      hsigma hchosen
    simp [hsame]
  · intro theta' htheta'
    funext x
    rcases x with ⟨_, a, rfl⟩
    have hthetaa : theta ⟨sigma a, ⟨a, rfl⟩⟩ = I a := by
      dsimp [theta]
      have hchosen :
          sigma (Classical.choose (show ∃ b : A, sigma b = sigma a from ⟨a, rfl⟩)) =
            sigma a :=
        Classical.choose_spec (show ∃ b : A, sigma b = sigma a from ⟨a, rfl⟩)
      have hsame :
          Classical.choose (show ∃ b : A, sigma b = sigma a from ⟨a, rfl⟩) = a :=
        hsigma hchosen
      simp [hsame]
    exact (htheta' a).trans hthetaa.symm

end Omega.Zeta
