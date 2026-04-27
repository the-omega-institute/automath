import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete data for the window-six sector/simplex/cone energy tomography package.

The three displayed energies are tied to quadratic coordinates, and the same coordinates are
calibrated by sector and cone angle data through a common positive scale. -/
structure conclusion_window6_sector_energy_simplex_cone_tomography_Data where
  sectorCoordinate : ℝ
  simplexCoordinate : ℝ
  coneCoordinate : ℝ
  sectorEnergy : ℝ
  simplexEnergy : ℝ
  coneEnergy : ℝ
  sectorAngle : ℝ
  coneAngle : ℝ
  scale : ℝ
  sectorEnergy_identity : sectorEnergy = sectorCoordinate ^ 2
  simplexEnergy_identity : simplexEnergy = simplexCoordinate ^ 2
  coneEnergy_identity : coneEnergy = coneCoordinate ^ 2
  sectorAngle_identity : sectorCoordinate ^ 2 = scale * sectorAngle
  coneAngle_identity : coneCoordinate ^ 2 = scale * coneAngle
  simplexQuadratic_balance : simplexCoordinate ^ 2 = sectorCoordinate ^ 2 + coneCoordinate ^ 2
  scale_pos : 0 < scale
  sectorAngle_nonneg : 0 ≤ sectorAngle
  coneAngle_pos : 0 < coneAngle

namespace conclusion_window6_sector_energy_simplex_cone_tomography_Data

noncomputable section

/-- The pair of sector/cone energies normalized by the simplex energy. -/
def conclusion_window6_sector_energy_simplex_cone_tomography_normalized_energy_pair
    (D : conclusion_window6_sector_energy_simplex_cone_tomography_Data) : ℝ × ℝ :=
  (D.sectorEnergy / D.simplexEnergy, D.coneEnergy / D.simplexEnergy)

/-- The standard closed line segment from the sector vertex to the cone vertex. -/
def conclusion_window6_sector_energy_simplex_cone_tomography_line_segment (p : ℝ × ℝ) :
    Prop :=
  0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 = 1

/-- The sector-to-cone normalized-energy ratio is the sector-to-cone angle ratio. -/
def conclusion_window6_sector_energy_simplex_cone_tomography_ratio_to_angle_formula
    (D : conclusion_window6_sector_energy_simplex_cone_tomography_Data) : Prop :=
  D.sectorEnergy / D.coneEnergy = D.sectorAngle / D.coneAngle

/-- Paper-facing statement: the normalized pair lies on the segment, and the ratio formula holds. -/
def conclusion_window6_sector_energy_simplex_cone_tomography_statement
    (D : conclusion_window6_sector_energy_simplex_cone_tomography_Data) : Prop :=
  conclusion_window6_sector_energy_simplex_cone_tomography_line_segment
      (conclusion_window6_sector_energy_simplex_cone_tomography_normalized_energy_pair D) ∧
    conclusion_window6_sector_energy_simplex_cone_tomography_ratio_to_angle_formula D

lemma conclusion_window6_sector_energy_simplex_cone_tomography_sectorEnergy_eq_scale_angle
    (D : conclusion_window6_sector_energy_simplex_cone_tomography_Data) :
    D.sectorEnergy = D.scale * D.sectorAngle := by
  calc
    D.sectorEnergy = D.sectorCoordinate ^ 2 := D.sectorEnergy_identity
    _ = D.scale * D.sectorAngle := D.sectorAngle_identity

lemma conclusion_window6_sector_energy_simplex_cone_tomography_coneEnergy_eq_scale_angle
    (D : conclusion_window6_sector_energy_simplex_cone_tomography_Data) :
    D.coneEnergy = D.scale * D.coneAngle := by
  calc
    D.coneEnergy = D.coneCoordinate ^ 2 := D.coneEnergy_identity
    _ = D.scale * D.coneAngle := D.coneAngle_identity

lemma conclusion_window6_sector_energy_simplex_cone_tomography_simplexEnergy_eq_sum
    (D : conclusion_window6_sector_energy_simplex_cone_tomography_Data) :
    D.simplexEnergy = D.sectorEnergy + D.coneEnergy := by
  calc
    D.simplexEnergy = D.simplexCoordinate ^ 2 := D.simplexEnergy_identity
    _ = D.sectorCoordinate ^ 2 + D.coneCoordinate ^ 2 := D.simplexQuadratic_balance
    _ = D.sectorEnergy + D.coneEnergy := by
          rw [D.sectorEnergy_identity, D.coneEnergy_identity]

lemma conclusion_window6_sector_energy_simplex_cone_tomography_simplexEnergy_pos
    (D : conclusion_window6_sector_energy_simplex_cone_tomography_Data) :
    0 < D.simplexEnergy := by
  have hsector :
      D.sectorEnergy = D.scale * D.sectorAngle :=
    D.conclusion_window6_sector_energy_simplex_cone_tomography_sectorEnergy_eq_scale_angle
  have hcone :
      D.coneEnergy = D.scale * D.coneAngle :=
    D.conclusion_window6_sector_energy_simplex_cone_tomography_coneEnergy_eq_scale_angle
  have hsum :
      D.simplexEnergy = D.sectorEnergy + D.coneEnergy :=
    D.conclusion_window6_sector_energy_simplex_cone_tomography_simplexEnergy_eq_sum
  have hangle_pos : 0 < D.sectorAngle + D.coneAngle :=
    add_pos_of_nonneg_of_pos D.sectorAngle_nonneg D.coneAngle_pos
  rw [hsum, hsector, hcone]
  nlinarith [D.scale_pos, hangle_pos]

lemma conclusion_window6_sector_energy_simplex_cone_tomography_normalized_pair_on_segment
    (D : conclusion_window6_sector_energy_simplex_cone_tomography_Data) :
    conclusion_window6_sector_energy_simplex_cone_tomography_line_segment
      (conclusion_window6_sector_energy_simplex_cone_tomography_normalized_energy_pair D) := by
  have hsum :
      D.simplexEnergy = D.sectorEnergy + D.coneEnergy :=
    D.conclusion_window6_sector_energy_simplex_cone_tomography_simplexEnergy_eq_sum
  have hs_nonneg : 0 ≤ D.sectorEnergy := by rw [D.sectorEnergy_identity]; positivity
  have hc_nonneg : 0 ≤ D.coneEnergy := by rw [D.coneEnergy_identity]; positivity
  have hsimplex_pos :
      0 < D.simplexEnergy :=
    D.conclusion_window6_sector_energy_simplex_cone_tomography_simplexEnergy_pos
  have hsimplex_nonneg : 0 ≤ D.simplexEnergy := le_of_lt hsimplex_pos
  refine ⟨?_, ?_, ?_⟩
  · exact div_nonneg hs_nonneg hsimplex_nonneg
  · exact div_nonneg hc_nonneg hsimplex_nonneg
  · rw [conclusion_window6_sector_energy_simplex_cone_tomography_normalized_energy_pair]
    have hne : D.simplexEnergy ≠ 0 := ne_of_gt hsimplex_pos
    calc
      D.sectorEnergy / D.simplexEnergy + D.coneEnergy / D.simplexEnergy =
          (D.sectorEnergy + D.coneEnergy) / D.simplexEnergy := by
            ring
      _ = D.simplexEnergy / D.simplexEnergy := by rw [← hsum]
      _ = 1 := by exact div_self hne

lemma conclusion_window6_sector_energy_simplex_cone_tomography_ratio_to_angle
    (D : conclusion_window6_sector_energy_simplex_cone_tomography_Data) :
    conclusion_window6_sector_energy_simplex_cone_tomography_ratio_to_angle_formula D := by
  have hsector :
      D.sectorEnergy = D.scale * D.sectorAngle :=
    D.conclusion_window6_sector_energy_simplex_cone_tomography_sectorEnergy_eq_scale_angle
  have hcone :
      D.coneEnergy = D.scale * D.coneAngle :=
    D.conclusion_window6_sector_energy_simplex_cone_tomography_coneEnergy_eq_scale_angle
  have hscale_ne : D.scale ≠ 0 := ne_of_gt D.scale_pos
  have hangle_ne : D.coneAngle ≠ 0 := ne_of_gt D.coneAngle_pos
  rw [conclusion_window6_sector_energy_simplex_cone_tomography_ratio_to_angle_formula,
    hsector, hcone]
  field_simp [hscale_ne, hangle_ne]

end

end conclusion_window6_sector_energy_simplex_cone_tomography_Data

open conclusion_window6_sector_energy_simplex_cone_tomography_Data

/-- Paper label: `thm:conclusion-window6-sector-energy-simplex-cone-tomography`. -/
theorem paper_conclusion_window6_sector_energy_simplex_cone_tomography
    (D : conclusion_window6_sector_energy_simplex_cone_tomography_Data) :
    conclusion_window6_sector_energy_simplex_cone_tomography_statement D := by
  exact
    ⟨D.conclusion_window6_sector_energy_simplex_cone_tomography_normalized_pair_on_segment,
      D.conclusion_window6_sector_energy_simplex_cone_tomography_ratio_to_angle⟩

end Omega.Conclusion
