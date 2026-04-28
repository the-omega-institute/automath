import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-time-part62d-rational-rose-minimal-prime-carrier`. -/
theorem paper_xi_time_part62d_rational_rose_minimal_prime_carrier {S : Finset Nat}
    (Feasible : Finset Nat → Prop) (hS : Feasible S)
    (hmin : ∀ T : Finset Nat, Feasible T → S ⊆ T) :
    Feasible S ∧ ∀ T : Finset Nat, T ⊂ S → ¬ Feasible T := by
  refine ⟨hS, ?_⟩
  intro T hTS hT
  exact hTS.2 (hmin T hT)

end Omega.Zeta
