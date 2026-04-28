import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-faithful-hidden-sector-must-be-nonabelian-and-nonhook`. -/
theorem paper_conclusion_faithful_hidden_sector_must_be_nonabelian_and_nonhook
    {Sector : Type} {faithful nonAbelian nonHook : Sector → Prop}
    (hArtin : ∀ s, faithful s → nonAbelian s)
    (hSchur : ∀ s, faithful s → nonHook s) :
    ∀ s, faithful s → nonAbelian s ∧ nonHook s := by
  intro s hs
  exact ⟨hArtin s hs, hSchur s hs⟩

end Omega.Conclusion
