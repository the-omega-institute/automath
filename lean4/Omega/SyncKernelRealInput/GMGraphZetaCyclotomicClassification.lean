import Mathlib.Tactic

namespace Omega.SyncKernelRealInput

/-- Paper label: `thm:gm-graph-zeta-cyclotomic-classification`. -/
theorem paper_gm_graph_zeta_cyclotomic_classification
    {χ : Type*} (trivial : χ)
    (hasCyclotomicFactor samePerronRadius : χ → Prop) (hasModObstruction : Prop)
    (hclass : ∀ c, c ≠ trivial → (hasCyclotomicFactor c ↔ samePerronRadius c))
    (hobs : hasModObstruction ↔ ∃ c, c ≠ trivial ∧ samePerronRadius c) :
    hasModObstruction ↔ ∃ c, c ≠ trivial ∧ hasCyclotomicFactor c := by
  constructor
  · intro h
    rcases hobs.mp h with ⟨c, hc_ne, hc_radius⟩
    exact ⟨c, hc_ne, (hclass c hc_ne).mpr hc_radius⟩
  · rintro ⟨c, hc_ne, hc_cyclo⟩
    exact hobs.mpr ⟨c, hc_ne, (hclass c hc_ne).mp hc_cyclo⟩

end Omega.SyncKernelRealInput
