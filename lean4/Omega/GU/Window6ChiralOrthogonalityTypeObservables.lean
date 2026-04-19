import Omega.GroupUnification.ChiralOrthogonalityTypeObservables

namespace Omega.GU

/-- Paper-facing `GU` wrapper: observables that factor through a `σ`-invariant type map remain
orthogonal to chiral anti-invariant observables.
    prop:window6-chiral-orthogonality-to-type-observables -/
theorem paper_window6_chiral_orthogonality_type_observables
    {alpha beta : Type*} [Fintype alpha] [DecidableEq alpha]
    (sigma : alpha → alpha) (hSigma : Function.Involutive sigma)
    (F : alpha → beta) (hF : ∀ x, F (sigma x) = F x)
    (gbar : beta → ℝ) (f : alpha → ℝ)
    (hf : ∀ x, f (sigma x) = -f x) :
    (∑ x, gbar (F x) * f x) = 0 := by
  have hg : ∀ x, (gbar ∘ F) (sigma x) = (gbar ∘ F) x := by
    intro x
    simp [Function.comp, hF x]
  simpa [Function.comp] using
    Omega.GroupUnification.paper_window6_chiral_orthogonality_type_observables_seeds
      sigma hSigma (gbar ∘ F) f hg hf

end Omega.GU
