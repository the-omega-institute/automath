namespace Omega.Zeta

/-- Paper label: `thm:xi-capacity-tail-histogram-moment-complete-statistic`. -/
theorem paper_xi_capacity_tail_histogram_moment_complete_statistic
    (Capacity Tail Histogram Moments : Prop) (hCT : Capacity <-> Tail)
    (hTH : Tail <-> Histogram) (hHM : Histogram <-> Moments) :
    Capacity <-> Tail /\ Histogram /\ Moments := by
  constructor
  · intro hCapacity
    have hTail : Tail := hCT.mp hCapacity
    have hHistogram : Histogram := hTH.mp hTail
    have hMoments : Moments := hHM.mp hHistogram
    exact ⟨hTail, hHistogram, hMoments⟩
  · intro hAll
    exact hCT.mpr hAll.1

end Omega.Zeta
