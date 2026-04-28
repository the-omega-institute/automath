import Mathlib.Logic.ExistsUnique

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-softcore-fixedm-wordtrace-spectrum-window-recovery`. -/
theorem paper_conclusion_softcore_fixedm_wordtrace_spectrum_window_recovery
    {Window Spectrum Multiplicity Background : Type}
    (recovers : Window → Spectrum → Multiplicity → Background → Prop) (window : Window)
    (hunique : ∃! data : Spectrum × Multiplicity × Background,
      recovers window data.1 data.2.1 data.2.2) :
    ∃! data : Spectrum × Multiplicity × Background,
      recovers window data.1 data.2.1 data.2.2 := by
  exact hunique

end Omega.Conclusion
