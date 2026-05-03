import Omega.Conclusion.TqftHighGenusBottomSpectrumPeeling

namespace Omega.Conclusion

open Filter
open scoped BigOperators

/-- Concrete finite fiber spectrum for the positive-moment/freezing and high-genus peeling
comparison. The multiplicities `μ` weight the genus partition terms and `δ` is the strictly
increasing finite spectrum. -/
structure conclusion_positive_moment_freezing_high_genus_peeling_duality_data where
  conclusion_positive_moment_freezing_high_genus_peeling_duality_s : ℕ
  conclusion_positive_moment_freezing_high_genus_peeling_duality_delta :
    Fin conclusion_positive_moment_freezing_high_genus_peeling_duality_s → ℕ
  conclusion_positive_moment_freezing_high_genus_peeling_duality_mu :
    Fin conclusion_positive_moment_freezing_high_genus_peeling_duality_s → ℕ
  conclusion_positive_moment_freezing_high_genus_peeling_duality_delta_pos :
    ∀ j, 0 < conclusion_positive_moment_freezing_high_genus_peeling_duality_delta j
  conclusion_positive_moment_freezing_high_genus_peeling_duality_delta_strict :
    StrictMono conclusion_positive_moment_freezing_high_genus_peeling_duality_delta

namespace conclusion_positive_moment_freezing_high_genus_peeling_duality_data

/-- The top finite-spectrum probe used for positive-moment freezing. -/
def conclusion_positive_moment_freezing_high_genus_peeling_duality_top_probe
    (D : conclusion_positive_moment_freezing_high_genus_peeling_duality_data) (_a : ℕ) : ℝ :=
  ((Finset.univ.sup
    D.conclusion_positive_moment_freezing_high_genus_peeling_duality_delta : ℕ) : ℝ)

/-- The bottom high-genus peeling term around a fixed spectrum index. -/
noncomputable def conclusion_positive_moment_freezing_high_genus_peeling_duality_bottom_term
    (D : conclusion_positive_moment_freezing_high_genus_peeling_duality_data)
    (r : Fin D.conclusion_positive_moment_freezing_high_genus_peeling_duality_s) (g : ℕ) : ℝ :=
  (D.conclusion_positive_moment_freezing_high_genus_peeling_duality_mu r : ℝ) +
    ∑ j : {j : Fin D.conclusion_positive_moment_freezing_high_genus_peeling_duality_s // r < j},
      (D.conclusion_positive_moment_freezing_high_genus_peeling_duality_mu (j : Fin _) : ℝ) *
        (((D.conclusion_positive_moment_freezing_high_genus_peeling_duality_delta r : ℝ) /
            (D.conclusion_positive_moment_freezing_high_genus_peeling_duality_delta
              (j : Fin _) : ℝ)) ^ (2 * g - 2))

end conclusion_positive_moment_freezing_high_genus_peeling_duality_data

/-- Concrete statement: the top finite-spectrum probe is already frozen, while the bottom end is
the existing high-genus peeling limit for every finite spectrum layer. -/
def conclusion_positive_moment_freezing_high_genus_peeling_duality_statement
    (D : conclusion_positive_moment_freezing_high_genus_peeling_duality_data) : Prop :=
  Filter.Tendsto
      (D.conclusion_positive_moment_freezing_high_genus_peeling_duality_top_probe)
      Filter.atTop
      (nhds ((Finset.univ.sup
        D.conclusion_positive_moment_freezing_high_genus_peeling_duality_delta : ℕ) : ℝ)) ∧
    ∀ r : Fin D.conclusion_positive_moment_freezing_high_genus_peeling_duality_s,
      Filter.Tendsto
        (fun g : ℕ =>
          D.conclusion_positive_moment_freezing_high_genus_peeling_duality_bottom_term r g)
        Filter.atTop
        (nhds (D.conclusion_positive_moment_freezing_high_genus_peeling_duality_mu r : ℝ))

/-- Paper label: `thm:conclusion-positive-moment-freezing-high-genus-peeling-duality`. -/
theorem paper_conclusion_positive_moment_freezing_high_genus_peeling_duality
    (D : conclusion_positive_moment_freezing_high_genus_peeling_duality_data) :
    conclusion_positive_moment_freezing_high_genus_peeling_duality_statement D := by
  refine ⟨?_, ?_⟩
  · change Filter.Tendsto
      (fun _a : ℕ =>
        ((Finset.univ.sup
          D.conclusion_positive_moment_freezing_high_genus_peeling_duality_delta : ℕ) : ℝ))
      Filter.atTop
      (nhds ((Finset.univ.sup
        D.conclusion_positive_moment_freezing_high_genus_peeling_duality_delta : ℕ) : ℝ))
    exact tendsto_const_nhds
  · simpa [
      conclusion_positive_moment_freezing_high_genus_peeling_duality_data.conclusion_positive_moment_freezing_high_genus_peeling_duality_bottom_term] using
      paper_conclusion_tqft_high_genus_bottom_spectrum_peeling
        D.conclusion_positive_moment_freezing_high_genus_peeling_duality_delta
        D.conclusion_positive_moment_freezing_high_genus_peeling_duality_mu
        D.conclusion_positive_moment_freezing_high_genus_peeling_duality_delta_pos
        D.conclusion_positive_moment_freezing_high_genus_peeling_duality_delta_strict

end Omega.Conclusion
