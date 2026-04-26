import Mathlib.Data.Nat.Basic

namespace Omega.Zeta

theorem paper_dephys_full_state_recovery_forces_trivial_index1 {A : Type} (E R : A → A)
    (index : (A → A) → ℕ) (hE : ∀ x, E (E x) = E x) (hR : ∀ x, R (E x) = x)
    (hindex : index id = 1) : E = id ∧ index E = 1 := by
  have hId : E = id := by
    funext x
    have hEx : R (E x) = E x := by
      calc
        R (E x) = R (E (E x)) := by rw [hE x]
        _ = E x := hR (E x)
    exact calc
      E x = R (E x) := hEx.symm
      _ = x := hR x
  exact ⟨hId, by simpa [hId] using hindex⟩

end Omega.Zeta
