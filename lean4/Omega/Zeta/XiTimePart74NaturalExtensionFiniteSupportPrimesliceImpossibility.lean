import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part74-natural-extension-finite-support-primeslice-impossibility`. -/
theorem paper_xi_time_part74_natural_extension_finite_support_primeslice_impossibility
    {Hist Code : Type*} (supportDepth : Code -> Nat) (encode : Hist -> Code)
    (hfinite : ∃ M : Nat, ∀ h : Hist, supportDepth (encode h) ≤ M)
    (hlower : Function.Injective encode -> ∀ M : Nat, ∃ h : Hist, M < supportDepth (encode h)) :
    ¬ Function.Injective encode := by
  intro hencode
  rcases hfinite with ⟨M, hM⟩
  rcases hlower hencode M with ⟨h, hh⟩
  exact (Nat.not_lt_of_ge (hM h)) hh

end Omega.Zeta
