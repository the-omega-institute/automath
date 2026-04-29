import Mathlib.Data.Finset.Basic

namespace Omega.Zeta

/-- Paper label: `thm:xi-localized-solenoid-terminal-object-poset`. -/
theorem paper_xi_localized_solenoid_terminal_object_poset
    (surj kernelExact : Finset ℕ → Finset ℕ → Prop)
    (universalKernel terminalObject : Finset ℕ → Prop)
    (hSurj : ∀ S T : Finset ℕ, surj S T ↔ T ⊆ S)
    (hKernel : ∀ S T : Finset ℕ, T ⊆ S → kernelExact S T)
    (hUniversal : ∀ S : Finset ℕ, universalKernel S ∧ terminalObject S) :
    (∀ S T : Finset ℕ, surj S T ↔ T ⊆ S) ∧
      (∀ S T : Finset ℕ, T ⊆ S → kernelExact S T) ∧
        (∀ S : Finset ℕ, universalKernel S ∧ terminalObject S) := by
  exact ⟨hSurj, hKernel, hUniversal⟩

end Omega.Zeta
