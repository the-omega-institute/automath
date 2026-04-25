import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.Conclusion.Window6RationalHomotopyInvertsTailTrichotomy
import Omega.Zeta.DerivedWindow6GaugeVolumeDefectIdentity

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-window6-rational-homotopy-determines-gauge-volume`. The odd
rational homotopy tail ranks `r₃ = 21`, `r₅ = 13`, `r₇ = 9` recover the histogram
`(n₂, n₃, n₄) = (8, 4, 9)`, which in turn fixes the gauge-group factorial product, its
abelianization rank, and the closed logarithmic gauge-volume formulas. -/
theorem paper_conclusion_window6_rational_homotopy_determines_gauge_volume
    (n2 n3 n4 : ℕ) (hr3 : 21 = n2 + n3 + n4) (hr5 : 13 = n3 + n4) (hr7 : 9 = n4) :
    n2 = 8 ∧
      n3 = 4 ∧
      n4 = 9 ∧
      2 * n2 + 3 * n3 + 4 * n4 = 64 ∧
      4 * n2 + 9 * n3 + 16 * n4 = 212 ∧
      Omega.Zeta.window6GaugeGroupOrder =
        Nat.factorial 2 ^ n2 * Nat.factorial 3 ^ n3 * Nat.factorial 4 ^ n4 ∧
      (n2 + n3 + n4 : ℕ) = 21 ∧
      Omega.Zeta.window6GaugeGroupOrder = 2 ^ 39 * 3 ^ 13 ∧
      Omega.Zeta.window6GaugeLogDensity = (39 * Real.log 2 + 13 * Real.log 3) / 64 ∧
      Omega.Zeta.window6GaugeVolumeDensity = (88 * Real.log 2 + 12 * Real.log 3) / 64 := by
  rcases
      paper_conclusion_window6_rational_homotopy_inverts_tail_trichotomy
        n2 n3 n4 21 13 9 hr3 hr5 hr7 with ⟨hn2, hn3, hn4⟩
  subst n4
  subst n3
  subst n2
  rcases Omega.Zeta.paper_derived_window6_gauge_volume_defect_identity with
    ⟨horder, hlog, hvol, _, _⟩
  refine ⟨rfl, rfl, rfl, by norm_num, by norm_num, ?_, by norm_num, horder, hlog, hvol⟩
  simp [Omega.Zeta.window6GaugeGroupOrder]

end Omega.Conclusion
