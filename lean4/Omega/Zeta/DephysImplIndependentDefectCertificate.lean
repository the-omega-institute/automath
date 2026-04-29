import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:dephys-impl-independent-defect-certificate`. -/
theorem paper_dephys_impl_independent_defect_certificate
    (RH : Prop) (D Dhat eps : Nat → ℝ)
    (sound : ∀ n, D n ≤ Dhat n + eps n)
    (hlim : ∀ η > 0, ∃ N, ∀ n ≥ N, Dhat n + eps n ≤ η)
    (repulsion : (∀ η > 0, ∃ n, D n ≤ η) → RH) :
    RH := by
  apply repulsion
  intro η hη
  obtain ⟨N, hN⟩ := hlim η hη
  exact ⟨N, le_trans (sound N) (hN N le_rfl)⟩

end Omega.Zeta
