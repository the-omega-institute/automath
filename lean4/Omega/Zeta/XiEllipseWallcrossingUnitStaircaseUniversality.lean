import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Concrete data for assembling a finite staircase from unit wall-crossing contributions. -/
structure XiEllipseWallcrossingUnitStaircaseUniversalityData where
  S : Finset ℝ
  t : ℝ
  residueContribution : ℝ → ℤ
  ellipseAverage : ℤ
  hsum : ellipseAverage = Finset.sum S (fun δ => residueContribution δ)
  hsingle :
    ∀ ⦃δ : ℝ⦄, δ ∈ S → residueContribution δ = (-1 : ℤ) + (if δ < t then 1 else 0)

/-- The total wall-crossing equals the filtered-cardinality staircase after adding back the
universal `-1` contribution from each singular jump. -/
def XiEllipseWallcrossingUnitStaircaseUniversalityData.unitStaircaseUniversality
    (D : XiEllipseWallcrossingUnitStaircaseUniversalityData) : Prop :=
  D.ellipseAverage + D.S.card = (D.S.filter fun δ => δ < D.t).card

/-- Summing the single-jump wall-crossing formula over a finite family produces the staircase
count of thresholds below the chosen time parameter.
    cor:xi-ellipse-wallcrossing-unit-staircase-universality -/
theorem paper_xi_ellipse_wallcrossing_unit_staircase_universality
    (D : XiEllipseWallcrossingUnitStaircaseUniversalityData) : D.unitStaircaseUniversality := by
  rw [XiEllipseWallcrossingUnitStaircaseUniversalityData.unitStaircaseUniversality, D.hsum]
  have hsum' :
      Finset.sum D.S (fun δ => D.residueContribution δ) =
        Finset.sum D.S (fun δ => (-1 : ℤ) + (if δ < D.t then 1 else 0)) := by
    refine Finset.sum_congr rfl ?_
    intro δ hδ
    exact D.hsingle hδ
  rw [hsum']
  calc
    (Finset.sum D.S (fun δ => (-1 : ℤ) + (if δ < D.t then 1 else 0))) + D.S.card
        = (Finset.sum D.S (fun _ => (-1 : ℤ)) +
            Finset.sum D.S (fun δ => (if δ < D.t then 1 else 0 : ℤ))) + D.S.card := by
            rw [Finset.sum_add_distrib]
    _ = (-(D.S.card : ℤ) + (D.S.filter fun δ => δ < D.t).card) + D.S.card := by
          simp
    _ = (D.S.filter fun δ => δ < D.t).card := by ring

end Omega.Zeta
