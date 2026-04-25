import Mathlib.Tactic
import Omega.Conclusion.NoncontractibleLossMod6Explicit

namespace Omega.POM

/-- Paper label: `thm:pom-max-noncontractible-fiber-mod6-phase`. The noncontractible fiber count
is already defined by the explicit `m mod 6` phase split, so each residue class rewrites to the
corresponding top-three closed form. -/
theorem paper_pom_max_noncontractible_fiber_mod6_phase :
    (∀ m : ℕ, 17 ≤ m → (m % 6 = 0 ∨ m % 6 = 4) →
      Omega.Conclusion.noncontractibleFiberCount m =
        Omega.Conclusion.noncontractibleMainFiberCount m) ∧
      (∀ m : ℕ, 17 ≤ m → (m % 6 = 1 ∨ m % 6 = 5) →
        Omega.Conclusion.noncontractibleFiberCount m =
          Omega.Conclusion.noncontractibleSecondFiberCount m) ∧
      (∀ m : ℕ, 17 ≤ m → (m % 6 = 2 ∨ m % 6 = 3) →
        Omega.Conclusion.noncontractibleFiberCount m =
          Omega.Conclusion.noncontractibleThirdFiberCount m) := by
  refine ⟨?_, ?_, ?_⟩
  · intro m hm hmod
    rcases hmod with h0 | h4
    · simp [Omega.Conclusion.noncontractibleFiberCount, h0]
    · simp [Omega.Conclusion.noncontractibleFiberCount, h4]
  · intro m hm hmod
    rcases hmod with h1 | h5
    · simp [Omega.Conclusion.noncontractibleFiberCount, h1]
    · simp [Omega.Conclusion.noncontractibleFiberCount, h5]
  · intro m hm hmod
    rcases hmod with h2 | h3
    · simp [Omega.Conclusion.noncontractibleFiberCount, h2]
    · simp [Omega.Conclusion.noncontractibleFiberCount, h3]

end Omega.POM
