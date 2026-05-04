import Omega.Zeta.XiTimePart60aComovingDefectFourierPronyLinearization

namespace Omega.Zeta

noncomputable section

/-- Paper label: `cor:xi-time-part60a-comoving-defect-minimal-sampling-sharp`. Distinct Prony
nodes give full Hankel rank through the Fourier--Prony package; the supplied recovery implications
then give Prony recovery and the height-window reconstruction. -/
theorem paper_xi_time_part60a_comoving_defect_minimal_sampling_sharp
    (h : xi_time_part60a_comoving_defect_fourier_prony_linearization_data)
    (shortSegmentsInsufficient prony2NSamplesRecover heightWindowRecover : Prop)
    (hdistinct : Function.Injective h.node) (hshort : shortSegmentsInsufficient)
    (hrecover : h.hankelRank = h.N → prony2NSamplesRecover)
    (hheight : prony2NSamplesRecover → heightWindowRecover) :
    shortSegmentsInsufficient ∧ prony2NSamplesRecover ∧ heightWindowRecover := by
  have hfullRank : h.hankelRank = h.N := h.hhankelRankEqDistinct hdistinct
  have hprony : prony2NSamplesRecover := hrecover hfullRank
  exact ⟨hshort, hprony, hheight hprony⟩

end

end Omega.Zeta
