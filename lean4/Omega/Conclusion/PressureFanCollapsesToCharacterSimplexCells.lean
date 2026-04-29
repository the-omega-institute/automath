import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete finite pressure-fan data for the character-simplex collapse theorem. -/
structure conclusion_pressure_fan_collapses_to_character_simplex_cells_Data where
  conclusion_pressure_fan_collapses_to_character_simplex_cells_q : ℕ
  conclusion_pressure_fan_collapses_to_character_simplex_cells_hq :
    0 < conclusion_pressure_fan_collapses_to_character_simplex_cells_q
  conclusion_pressure_fan_collapses_to_character_simplex_cells_vertex :
    Fin conclusion_pressure_fan_collapses_to_character_simplex_cells_q → ℝ
  conclusion_pressure_fan_collapses_to_character_simplex_cells_weight :
    Finset (Fin conclusion_pressure_fan_collapses_to_character_simplex_cells_q) →
      Fin conclusion_pressure_fan_collapses_to_character_simplex_cells_q → ℝ
  conclusion_pressure_fan_collapses_to_character_simplex_cells_maximizers :
    (Fin conclusion_pressure_fan_collapses_to_character_simplex_cells_q → ℝ) →
      Finset (Fin conclusion_pressure_fan_collapses_to_character_simplex_cells_q)
  conclusion_pressure_fan_collapses_to_character_simplex_cells_schurLimit :
    (Fin conclusion_pressure_fan_collapses_to_character_simplex_cells_q → ℝ) → ℝ
  conclusion_pressure_fan_collapses_to_character_simplex_cells_weight_zero_off_cell :
    ∀ (R : Finset (Fin conclusion_pressure_fan_collapses_to_character_simplex_cells_q))
      (ν : Fin conclusion_pressure_fan_collapses_to_character_simplex_cells_q),
        ν ∉ R →
          conclusion_pressure_fan_collapses_to_character_simplex_cells_weight R ν = 0
  conclusion_pressure_fan_collapses_to_character_simplex_cells_weight_positive_on_cell :
    ∀ (R : Finset (Fin conclusion_pressure_fan_collapses_to_character_simplex_cells_q))
      (ν : Fin conclusion_pressure_fan_collapses_to_character_simplex_cells_q),
        R.Nonempty →
          ν ∈ R →
            0 < conclusion_pressure_fan_collapses_to_character_simplex_cells_weight R ν
  conclusion_pressure_fan_collapses_to_character_simplex_cells_weight_sum_one :
    ∀ R : Finset (Fin conclusion_pressure_fan_collapses_to_character_simplex_cells_q),
      R.Nonempty →
        Finset.sum R
          (fun ν =>
            conclusion_pressure_fan_collapses_to_character_simplex_cells_weight R ν) = 1
  conclusion_pressure_fan_collapses_to_character_simplex_cells_schurLimit_eq_barycenter :
    ∀ p : Fin conclusion_pressure_fan_collapses_to_character_simplex_cells_q → ℝ,
      (conclusion_pressure_fan_collapses_to_character_simplex_cells_maximizers p).Nonempty →
        conclusion_pressure_fan_collapses_to_character_simplex_cells_schurLimit p =
          Finset.sum (conclusion_pressure_fan_collapses_to_character_simplex_cells_maximizers p)
            (fun ν =>
            conclusion_pressure_fan_collapses_to_character_simplex_cells_weight
                (conclusion_pressure_fan_collapses_to_character_simplex_cells_maximizers p) ν *
              conclusion_pressure_fan_collapses_to_character_simplex_cells_vertex ν)

/-- The barycenter attached to a whole maximizer cell. -/
def conclusion_pressure_fan_collapses_to_character_simplex_cells_barycenter
    (D : conclusion_pressure_fan_collapses_to_character_simplex_cells_Data)
    (R : Finset (Fin D.conclusion_pressure_fan_collapses_to_character_simplex_cells_q)) : ℝ :=
  Finset.sum R (fun ν =>
    D.conclusion_pressure_fan_collapses_to_character_simplex_cells_weight R ν *
      D.conclusion_pressure_fan_collapses_to_character_simplex_cells_vertex ν)

/-- Relative-interior membership expressed by strictly positive barycentric weights on the face. -/
def conclusion_pressure_fan_collapses_to_character_simplex_cells_relativeInterior
    (D : conclusion_pressure_fan_collapses_to_character_simplex_cells_Data)
    (R : Finset (Fin D.conclusion_pressure_fan_collapses_to_character_simplex_cells_q))
    (x : ℝ) : Prop :=
  ∃ w : Fin D.conclusion_pressure_fan_collapses_to_character_simplex_cells_q → ℝ,
    (∀ ν, ν ∈ R → 0 < w ν) ∧
      (∀ ν, ν ∉ R → w ν = 0) ∧
      (Finset.sum R (fun ν => w ν) = 1) ∧
      x =
        Finset.sum R
          (fun ν => w ν * D.conclusion_pressure_fan_collapses_to_character_simplex_cells_vertex ν)

/-- Paper-facing statement: the Schur limit is constant on each pressure-fan cell, singleton
cells freeze to their character vertex, and multiphase cells land in the relative interior. -/
def conclusion_pressure_fan_collapses_to_character_simplex_cells_Statement
    (D : conclusion_pressure_fan_collapses_to_character_simplex_cells_Data) : Prop :=
  ∀ R : Finset (Fin D.conclusion_pressure_fan_collapses_to_character_simplex_cells_q),
    R.Nonempty →
      (∃ p : Fin D.conclusion_pressure_fan_collapses_to_character_simplex_cells_q → ℝ,
        D.conclusion_pressure_fan_collapses_to_character_simplex_cells_maximizers p = R) →
        (∀ p p' : Fin D.conclusion_pressure_fan_collapses_to_character_simplex_cells_q → ℝ,
          D.conclusion_pressure_fan_collapses_to_character_simplex_cells_maximizers p = R →
            D.conclusion_pressure_fan_collapses_to_character_simplex_cells_maximizers p' = R →
              D.conclusion_pressure_fan_collapses_to_character_simplex_cells_schurLimit p =
                D.conclusion_pressure_fan_collapses_to_character_simplex_cells_schurLimit p') ∧
          (∀ p : Fin D.conclusion_pressure_fan_collapses_to_character_simplex_cells_q → ℝ,
            D.conclusion_pressure_fan_collapses_to_character_simplex_cells_maximizers p = R →
              D.conclusion_pressure_fan_collapses_to_character_simplex_cells_schurLimit p =
                conclusion_pressure_fan_collapses_to_character_simplex_cells_barycenter D R) ∧
          (∀ (ν : Fin D.conclusion_pressure_fan_collapses_to_character_simplex_cells_q)
            (p : Fin D.conclusion_pressure_fan_collapses_to_character_simplex_cells_q → ℝ),
              R = {ν} →
                D.conclusion_pressure_fan_collapses_to_character_simplex_cells_maximizers p = R →
                  D.conclusion_pressure_fan_collapses_to_character_simplex_cells_schurLimit p =
                    D.conclusion_pressure_fan_collapses_to_character_simplex_cells_vertex ν) ∧
          (2 ≤ R.card →
            ∀ p : Fin D.conclusion_pressure_fan_collapses_to_character_simplex_cells_q → ℝ,
              D.conclusion_pressure_fan_collapses_to_character_simplex_cells_maximizers p = R →
                conclusion_pressure_fan_collapses_to_character_simplex_cells_relativeInterior D R
                  (D.conclusion_pressure_fan_collapses_to_character_simplex_cells_schurLimit p))

/-- Paper label: `thm:conclusion-pressure-fan-collapses-to-character-simplex-cells`. -/
theorem paper_conclusion_pressure_fan_collapses_to_character_simplex_cells
    (D : conclusion_pressure_fan_collapses_to_character_simplex_cells_Data) :
    conclusion_pressure_fan_collapses_to_character_simplex_cells_Statement D := by
  intro R hR _hcell
  let bary :=
    conclusion_pressure_fan_collapses_to_character_simplex_cells_barycenter D R
  have hformula :
      ∀ p : Fin D.conclusion_pressure_fan_collapses_to_character_simplex_cells_q → ℝ,
        D.conclusion_pressure_fan_collapses_to_character_simplex_cells_maximizers p = R →
          D.conclusion_pressure_fan_collapses_to_character_simplex_cells_schurLimit p = bary := by
    intro p hp
    have hp_nonempty :
        (D.conclusion_pressure_fan_collapses_to_character_simplex_cells_maximizers p).Nonempty := by
      simpa [hp] using hR
    have hlimit :=
      D.conclusion_pressure_fan_collapses_to_character_simplex_cells_schurLimit_eq_barycenter p
        hp_nonempty
    simpa [bary, conclusion_pressure_fan_collapses_to_character_simplex_cells_barycenter, hp]
      using hlimit
  refine ⟨?_, hformula, ?_, ?_⟩
  · intro p p' hp hp'
    exact (hformula p hp).trans (hformula p' hp').symm
  · intro ν p hsingleton hp
    have hweight :
        D.conclusion_pressure_fan_collapses_to_character_simplex_cells_weight R ν = 1 := by
      have hsum :=
        D.conclusion_pressure_fan_collapses_to_character_simplex_cells_weight_sum_one R hR
      simpa [hsingleton] using hsum
    calc
      D.conclusion_pressure_fan_collapses_to_character_simplex_cells_schurLimit p = bary :=
        hformula p hp
      _ = D.conclusion_pressure_fan_collapses_to_character_simplex_cells_weight R ν *
          D.conclusion_pressure_fan_collapses_to_character_simplex_cells_vertex ν := by
        simp [bary, conclusion_pressure_fan_collapses_to_character_simplex_cells_barycenter,
          hsingleton]
      _ = D.conclusion_pressure_fan_collapses_to_character_simplex_cells_vertex ν := by
        simp [hweight]
  · intro _hcard p hp
    refine
      ⟨D.conclusion_pressure_fan_collapses_to_character_simplex_cells_weight R, ?_, ?_, ?_, ?_⟩
    · intro ν hν
      exact
        D.conclusion_pressure_fan_collapses_to_character_simplex_cells_weight_positive_on_cell R ν
          hR hν
    · intro ν hν
      exact
        D.conclusion_pressure_fan_collapses_to_character_simplex_cells_weight_zero_off_cell R ν hν
    · exact D.conclusion_pressure_fan_collapses_to_character_simplex_cells_weight_sum_one R hR
    · exact hformula p hp

end Omega.Conclusion
