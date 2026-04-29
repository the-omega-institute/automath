import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete finite data for the window-`6` anomaly determinant shadow. The `21` hidden standard
blocks are indexed by `Fin 21`; a subset of blocks detects exactly the coordinates it contains. -/
structure conclusion_window6_anomaly_determinant_shadow_data where
  conclusion_window6_anomaly_determinant_shadow_anomaly_signature : Fin 21 → ℤ
  conclusion_window6_anomaly_determinant_shadow_determinant_shadow : Fin 21 → ℤ
  conclusion_window6_anomaly_determinant_shadow_hidden_standard_blocks : Finset (Fin 21)
  conclusion_window6_anomaly_determinant_shadow_fiberwise_determinant_identity :
    ∀ w : Fin 21,
      conclusion_window6_anomaly_determinant_shadow_anomaly_signature w =
        conclusion_window6_anomaly_determinant_shadow_determinant_shadow w
  conclusion_window6_anomaly_determinant_shadow_hidden_blocks_complete :
    conclusion_window6_anomaly_determinant_shadow_hidden_standard_blocks = Finset.univ

/-- The anomaly signature vector equals the vector of determinants on hidden standard blocks. -/
def conclusion_window6_anomaly_determinant_shadow_data.signature_eq_determinant_shadow
    (D : conclusion_window6_anomaly_determinant_shadow_data) : Prop :=
  D.conclusion_window6_anomaly_determinant_shadow_anomaly_signature =
    D.conclusion_window6_anomaly_determinant_shadow_determinant_shadow

/-- A chosen direct sum of hidden standard blocks detects coordinate `w` precisely when the block
for `w` is still present. -/
def conclusion_window6_anomaly_determinant_shadow_data.detects_anomaly_coordinate
    (_D : conclusion_window6_anomaly_determinant_shadow_data) (blocks : Finset (Fin 21))
    (w : Fin 21) : Prop :=
  w ∈ blocks

/-- All `21` hidden standard blocks are present, and deleting any one of them makes the
corresponding anomaly coordinate undetectable. -/
def conclusion_window6_anomaly_determinant_shadow_data.hidden_summand_minimal
    (D : conclusion_window6_anomaly_determinant_shadow_data) : Prop :=
  (∀ w : Fin 21,
    D.detects_anomaly_coordinate
      D.conclusion_window6_anomaly_determinant_shadow_hidden_standard_blocks w) ∧
    ∀ w : Fin 21,
      ¬ D.detects_anomaly_coordinate
        (D.conclusion_window6_anomaly_determinant_shadow_hidden_standard_blocks.erase w) w

/-- Paper label: `thm:conclusion-window6-anomaly-determinant-shadow`. -/
theorem paper_conclusion_window6_anomaly_determinant_shadow
    (D : conclusion_window6_anomaly_determinant_shadow_data) :
    D.signature_eq_determinant_shadow ∧ D.hidden_summand_minimal := by
  constructor
  · funext w
    exact D.conclusion_window6_anomaly_determinant_shadow_fiberwise_determinant_identity w
  · constructor
    · intro w
      simp [conclusion_window6_anomaly_determinant_shadow_data.detects_anomaly_coordinate,
        D.conclusion_window6_anomaly_determinant_shadow_hidden_blocks_complete]
    · intro w
      simp [conclusion_window6_anomaly_determinant_shadow_data.detects_anomaly_coordinate]

end Omega.Conclusion
