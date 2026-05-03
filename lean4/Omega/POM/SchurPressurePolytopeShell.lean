import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `cor:pom-schur-pressure-polytope-shell`. Over a finite support, every
linear score has a maximizing support point. -/
theorem paper_pom_schur_pressure_polytope_shell {ι : Type*} [Fintype ι] [Nonempty ι]
    (q : ℕ) (c : ι → Fin q → ℝ) (p : Fin q → ℝ) :
    ∃ ν₀ : ι, ∀ ν : ι,
      (∑ j : Fin q, c ν j * p j) ≤ ∑ j : Fin q, c ν₀ j * p j := by
  classical
  rcases Finset.exists_max_image (Finset.univ : Finset ι)
      (fun ν => ∑ j : Fin q, c ν j * p j) Finset.univ_nonempty with
    ⟨ν₀, _hν₀, hν₀max⟩
  exact ⟨ν₀, fun ν => hν₀max ν (Finset.mem_univ ν)⟩

end Omega.POM
