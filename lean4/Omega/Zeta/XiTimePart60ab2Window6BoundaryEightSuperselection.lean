import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part60ab2-window6-boundary-eight-superselection`. -/
theorem paper_xi_time_part60ab2_window6_boundary_eight_superselection
    {Sector V : Type} [Fintype Sector] [DecidableEq Sector] (component : Sector → Set V)
    (hcard : Fintype.card Sector = 8)
    (hcover : ∀ v : V, ∃ χ, v ∈ component χ)
    (hdisj : ∀ χ ψ, χ ≠ ψ → Disjoint (component χ) (component ψ))
    (hnonempty : ∀ χ, (component χ).Nonempty) :
    Fintype.card Sector = 8 ∧ (∀ χ, (component χ).Nonempty) ∧
      (∀ v : V, ∃! χ, v ∈ component χ) := by
  refine ⟨hcard, hnonempty, ?_⟩
  intro v
  rcases hcover v with ⟨χ, hχ⟩
  refine ⟨χ, hχ, ?_⟩
  intro ψ hψ
  by_contra hne
  have hχψ : χ ≠ ψ := by
    intro h
    exact hne h.symm
  exact (Set.disjoint_left.mp (hdisj χ ψ hχψ)) hχ hψ

end Omega.Zeta
