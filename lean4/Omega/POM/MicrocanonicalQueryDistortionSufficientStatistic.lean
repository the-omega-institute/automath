import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `prop:pom-microcanonical-query-distortion-sufficient-statistic`. If the posterior
is constant on each residual-summary fiber, then every success functional of the posterior factors
through the residual summary. -/
theorem paper_pom_microcanonical_query_distortion_sufficient_statistic
    {Trace Summary Posterior Rate : Type} [Nonempty Rate]
    (summary : Trace → Summary) (posterior : Trace → Posterior) (success : Posterior → Rate)
    (h : ∀ t₁ t₂, summary t₁ = summary t₂ → posterior t₁ = posterior t₂) :
    ∃ Φ : Summary → Rate, ∀ t, Φ (summary t) = success (posterior t) := by
  classical
  refine ⟨fun s =>
    if hs : ∃ t, summary t = s then success (posterior (Classical.choose hs))
    else Classical.choice inferInstance, ?_⟩
  intro t
  have hs : ∃ u, summary u = summary t := ⟨t, rfl⟩
  simp only [dif_pos hs]
  exact congrArg success (h (Classical.choose hs) t (Classical.choose_spec hs))

end Omega.POM
