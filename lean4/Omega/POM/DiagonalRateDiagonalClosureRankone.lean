import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

/-- Paper label: `prop:pom-diagonal-rate-diagonal-closure-rankone`. -/
theorem paper_pom_diagonal_rate_diagonal_closure_rankone {α : Type*} [Fintype α]
    [DecidableEq α] (κ : ℚ) (t : α → ℚ) :
    let pom_diagonal_rate_diagonal_closure_rankone_pi := fun x => 1 / (t x - κ)
    let pom_diagonal_rate_diagonal_closure_rankone_K := fun x y =>
      if x = y then
        (1 + κ) / t x
      else
        ((t x - κ) / t x) * pom_diagonal_rate_diagonal_closure_rankone_pi y
    (∑ x, pom_diagonal_rate_diagonal_closure_rankone_pi x = 1) ->
      (∀ x, pom_diagonal_rate_diagonal_closure_rankone_K x x = (1 + κ) / t x) ∧
        (∀ x y, x ≠ y ->
          pom_diagonal_rate_diagonal_closure_rankone_K x y =
            ((t x - κ) / t x) * pom_diagonal_rate_diagonal_closure_rankone_pi y) := by
  dsimp
  intro _hπ
  refine ⟨?_, ?_⟩
  · intro x
    simp
  · intro x y hxy
    simp [hxy]

end Omega.POM
