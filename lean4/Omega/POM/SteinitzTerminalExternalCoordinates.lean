import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `prop:pom-steinitz-terminal-external-coordinates`. The valuation profile itself
is the unique injective external-coordinate map whenever profiles separate points. -/
theorem paper_pom_steinitz_terminal_external_coordinates {Q : Type} [CommMonoid Q]
    (v : ℕ → Q → ℕ) (hsep : Function.Injective (fun u : Q => fun m : ℕ => v m u)) :
    ∃! iota : Q → (ℕ → ℕ), Function.Injective iota ∧ ∀ u m, iota u m = v m u := by
  refine ⟨fun u m => v m u, ?_, ?_⟩
  · exact ⟨hsep, fun _ _ => rfl⟩
  · intro iota hiota
    ext u m
    exact hiota.2 u m

end Omega.POM
