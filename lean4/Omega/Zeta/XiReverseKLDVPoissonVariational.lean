import Mathlib

namespace Omega.Zeta

/-- Paper label: `thm:xi-reversekl-dv-poisson-variational`.
The Donsker--Varadhan variational package consists of the supremum representation together with an
attaining optimizer witness. -/
theorem paper_xi_reversekl_dv_poisson_variational {α : Type} (dual : Set α) (objective : α → ℝ)
    (Hr : ℝ) (hRep : Hr = sSup (Set.image objective dual))
    (hOpt : ∃ f ∈ dual, objective f = Hr) :
    Hr = sSup (Set.image objective dual) ∧ ∃ f ∈ dual, objective f = Hr := by
  exact ⟨hRep, hOpt⟩

end Omega.Zeta
