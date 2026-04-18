import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Omega.GU.Window6FamilyProjectionWequivariantUniqueness

open scoped BigOperators

namespace Omega.GU

/-- The `Fin 3` quotient attached to the window-6 family projection splits into the constant mode
and the zero-sum spherical mode. This is the concrete two-mode decomposition underlying the
paper's Gelfand/Hecke discussion.
    thm:window6-family-projection-spherical-hecke-two-modes -/
theorem paper_window6_family_projection_spherical_hecke_two_modes (f : Fin 3 → ℂ) :
    ∃ c : ℂ, ∃ g : Fin 3 → ℂ, f = (fun i => c + g i) ∧ (∑ i, g i = 0) := by
  refine ⟨(f 0 + f 1 + f 2) / 3, fun i => f i - (f 0 + f 1 + f 2) / 3, ?_⟩
  refine ⟨?_, ?_⟩
  · funext i
    ring
  · simp [Fin.sum_univ_three]
    ring

end Omega.GU
