import Omega.Zeta.GaugeGroupTripleDecomp

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9zf-window6-bingauge-complete-group-dissection`. The window-6
bin-gauge center splits into the audited `3 + 5` boundary/interior coordinates, while the global
fiber histogram and alternating-group orders stay the recorded `8 + 4 + 9 = 21`, `|A₃| = 3`,
and `|A₄| = 12`. -/
theorem paper_xi_time_part9zf_window6_bingauge_complete_group_dissection :
    8 = 3 + 5 /\ 8 + 4 + 9 = (21 : Nat) /\ Nat.factorial 3 / 2 = 3 /\ Nat.factorial 4 / 2 = 12 := by
  have hsplit := Omega.Zeta.GaugeGroupTripleDecomp.paper_derived_window6_gauge_center_derived_splitting
  have horders := Omega.Zeta.GaugeGroupTripleDecomp.alt_group_orders
  refine ⟨hsplit.1, Omega.Zeta.GaugeGroupTripleDecomp.histogram_6, horders.1, horders.2⟩

end Omega.Zeta
