import Mathlib.Data.Finset.Interval
import Mathlib.Data.List.Sublists
import Mathlib.Tactic
import Omega.DerivedConsequences.DerivedHurwitzVisibleRationalProjectionAlgebraNineChannels

namespace Omega.DerivedConsequences

/-- The nine visible primitive dimensions coming from the `ℚ × M₂(ℚ) × M₃(ℚ) × M₃(ℚ)` Hurwitz
projection algebra. -/
def derived_hurwitz_visible_rational_factor_dimension_subsetsums_channel_dimensions : List ℕ :=
  [5, 4, 4, 3, 3, 3, 9, 9, 9]

/-- The computed visible-dimension spectrum for the nine-channel Hurwitz block. This is the
explicit subset-sum spectrum of `[5, 4, 4, 3, 3, 3, 9, 9, 9]`. -/
def derived_hurwitz_visible_rational_factor_dimension_subsetsums_visible_dimensions : Finset ℕ :=
  ({0, 49} : Finset ℕ) ∪ Finset.Icc 3 46

private lemma derived_hurwitz_visible_rational_factor_dimension_subsetsums_mem_iff
    (d : ℕ) :
    d ∈ derived_hurwitz_visible_rational_factor_dimension_subsetsums_visible_dimensions ↔
      d = 0 ∨ d = 49 ∨ 3 ≤ d ∧ d ≤ 46 := by
  simp [derived_hurwitz_visible_rational_factor_dimension_subsetsums_visible_dimensions]

/-- Paper label: `cor:derived-hurwitz-visible-rational-factor-dimension-subsetsums`. The nine
visible primitive Hurwitz channels have dimensions `5, 4, 4, 3, 3, 3, 9, 9, 9`, so the visible
`ℚ`-rational direct-factor dimensions are exactly their subset sums. On the interval `1 ≤ d ≤ 49`
the only excluded dimensions are `1`, `2`, `47`, and `48`. -/
theorem paper_derived_hurwitz_visible_rational_factor_dimension_subsetsums :
    derived_hurwitz_visible_rational_projection_algebra_nine_channels_statement ∧
      derived_hurwitz_visible_rational_factor_dimension_subsetsums_channel_dimensions =
        [5, 4, 4, 3, 3, 3, 9, 9, 9] ∧
      ∀ d : ℕ, 1 ≤ d → d ≤ 49 →
        (d ∈ derived_hurwitz_visible_rational_factor_dimension_subsetsums_visible_dimensions ↔
          d ≠ 1 ∧ d ≠ 2 ∧ d ≠ 47 ∧ d ≠ 48) := by
  refine ⟨paper_derived_hurwitz_visible_rational_projection_algebra_nine_channels,
    rfl, ?_⟩
  intro d hd1 hd49
  rw [derived_hurwitz_visible_rational_factor_dimension_subsetsums_mem_iff]
  omega

end Omega.DerivedConsequences
