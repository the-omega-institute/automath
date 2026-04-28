import Omega.Conclusion.Window6SigmaGeoFourblockNormalForm

namespace Omega.Conclusion

/-- The characteristic-factor shadow of the four blocks
`A_{Q_4}, A_{Q_4}, A_{Q_4}+2I, A_{Q_4}-2I`. -/
def conclusion_window6_centerband_doubling_charpoly_factorization : Prop :=
  window6SigmaGeoAdjacencyBlockForm

/-- The audited center-band factors in the window-`6` four-block normal form. -/
def conclusion_window6_centerband_doubling_center_band_factors : List Int :=
  [4, 4]

/-- The two shifted side-band factors in the same normal form. -/
def conclusion_window6_centerband_doubling_shifted_band_factors : List Int :=
  [6, 2]

/-- The center band occurs twice, once in each unshifted block. -/
def conclusion_window6_centerband_doubling_center_band_multiplicity_two : Prop :=
  conclusion_window6_centerband_doubling_center_band_factors.length = 2 ∧
    conclusion_window6_centerband_doubling_center_band_factors ++
        conclusion_window6_centerband_doubling_shifted_band_factors =
      window6SigmaGeoAdjacencyDiagonal

/-- Paper label: `cor:conclusion-window6-centerband-doubling`. -/
theorem paper_conclusion_window6_centerband_doubling :
    conclusion_window6_centerband_doubling_charpoly_factorization ∧
      conclusion_window6_centerband_doubling_center_band_multiplicity_two := by
  rcases paper_conclusion_window6_sigma_geo_fourblock_normal_form with ⟨_, hBlock, _⟩
  refine ⟨hBlock, ?_⟩
  unfold conclusion_window6_centerband_doubling_center_band_multiplicity_two
    conclusion_window6_centerband_doubling_center_band_factors
    conclusion_window6_centerband_doubling_shifted_band_factors
  constructor
  · rfl
  · unfold window6SigmaGeoAdjacencyDiagonal
    rfl

end Omega.Conclusion
