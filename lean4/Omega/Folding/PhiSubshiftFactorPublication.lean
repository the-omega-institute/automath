import Omega.Folding.PhiSubshiftFactor

namespace Omega.Folding

variable {A B : Type*}

set_option maxHeartbeats 400000 in
/-- Publication-facing seed for the factor-map property of `Φ_m` on subshifts.
    prop:Phi-m-factor -/
theorem paper_resolution_phi_m_factor_seeds :
    ShiftInvariant (Set.univ : Set (ℤ → A)) ∧
    ShiftInvariant (∅ : Set (ℤ → A)) ∧
    (∀ (m : ℕ) (f : (Fin m → A) → B) (S : Set (ℤ → A)),
      ShiftInvariant S → ShiftInvariant (slideBlockCode m f '' S)) ∧
    (∀ (m : ℕ) (f : (Fin m → A) → B) (S : Set (ℤ → A)),
      ∀ t ∈ slideBlockCode m f '' S, ∃ s ∈ S, slideBlockCode m f s = t) :=
  paper_Phi_m_factor_on_subshift

end Omega.Folding
