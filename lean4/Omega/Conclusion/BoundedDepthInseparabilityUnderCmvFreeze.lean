import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete finite-window stabilization data for bounded-depth CMV/Toeplitz certificates.
For each certificate depth `N`, the row `window N L` records the finite observables available at
layer `L`, and `freezeAt N i` is the point after which coordinate `i` has frozen to its limit. -/
structure conclusion_bounded_depth_inseparability_under_cmv_freeze_data where
  conclusion_bounded_depth_inseparability_under_cmv_freeze_window :
    (N : ℕ) → ℕ → Fin (N + 1) → Bool
  conclusion_bounded_depth_inseparability_under_cmv_freeze_limitWindow :
    (N : ℕ) → Fin (N + 1) → Bool
  conclusion_bounded_depth_inseparability_under_cmv_freeze_freezeAt :
    (N : ℕ) → Fin (N + 1) → ℕ
  conclusion_bounded_depth_inseparability_under_cmv_freeze_freeze :
    ∀ (N : ℕ) (i : Fin (N + 1)) (L : ℕ),
      conclusion_bounded_depth_inseparability_under_cmv_freeze_freezeAt N i ≤ L →
        conclusion_bounded_depth_inseparability_under_cmv_freeze_window N L i =
          conclusion_bounded_depth_inseparability_under_cmv_freeze_limitWindow N i
  conclusion_bounded_depth_inseparability_under_cmv_freeze_certificate :
    (N : ℕ) → (Fin (N + 1) → Bool) → Bool
  conclusion_bounded_depth_inseparability_under_cmv_freeze_detectionDepth : ℕ → ℕ
  conclusion_bounded_depth_inseparability_under_cmv_freeze_detects_at_bounded_depth :
    ∀ B L : ℕ,
      conclusion_bounded_depth_inseparability_under_cmv_freeze_detectionDepth L ≤ B →
        conclusion_bounded_depth_inseparability_under_cmv_freeze_certificate B
          (conclusion_bounded_depth_inseparability_under_cmv_freeze_window B L) = true
  conclusion_bounded_depth_inseparability_under_cmv_freeze_limit_blind :
    ∀ B : ℕ,
      conclusion_bounded_depth_inseparability_under_cmv_freeze_certificate B
        (conclusion_bounded_depth_inseparability_under_cmv_freeze_limitWindow B) = false

namespace conclusion_bounded_depth_inseparability_under_cmv_freeze_data

/-- The stabilization threshold for the finite window of depth `N`. -/
def conclusion_bounded_depth_inseparability_under_cmv_freeze_stabilizationBound
    (D : conclusion_bounded_depth_inseparability_under_cmv_freeze_data) (N : ℕ) : ℕ :=
  Finset.univ.sup (D.conclusion_bounded_depth_inseparability_under_cmv_freeze_freezeAt N)

/-- A bounded-depth certificate is eventually constant, and persistent detection cannot remain
inside any fixed finite window. -/
def eventually_constant_and_detection_depth_tends_to_infinity
    (D : conclusion_bounded_depth_inseparability_under_cmv_freeze_data) : Prop :=
  (∀ N : ℕ,
    ∃ L0 b,
      ∀ L : ℕ,
        L0 ≤ L →
          D.conclusion_bounded_depth_inseparability_under_cmv_freeze_certificate N
              (D.conclusion_bounded_depth_inseparability_under_cmv_freeze_window N L) = b) ∧
    ∀ B : ℕ,
      ∃ L0,
        ∀ L : ℕ,
          L0 ≤ L →
            B < D.conclusion_bounded_depth_inseparability_under_cmv_freeze_detectionDepth L

lemma conclusion_bounded_depth_inseparability_under_cmv_freeze_window_stabilizes
    (D : conclusion_bounded_depth_inseparability_under_cmv_freeze_data) (N L : ℕ)
    (hL : D.conclusion_bounded_depth_inseparability_under_cmv_freeze_stabilizationBound N ≤ L) :
    D.conclusion_bounded_depth_inseparability_under_cmv_freeze_window N L =
      D.conclusion_bounded_depth_inseparability_under_cmv_freeze_limitWindow N := by
  funext i
  exact D.conclusion_bounded_depth_inseparability_under_cmv_freeze_freeze N i L
    (Nat.le_trans
      (Finset.le_sup (f := D.conclusion_bounded_depth_inseparability_under_cmv_freeze_freezeAt N)
        (Finset.mem_univ i))
      hL)

end conclusion_bounded_depth_inseparability_under_cmv_freeze_data

/-- Paper label: `thm:conclusion-bounded-depth-inseparability-under-cmv-freeze`. -/
theorem paper_conclusion_bounded_depth_inseparability_under_cmv_freeze
    (D : conclusion_bounded_depth_inseparability_under_cmv_freeze_data) :
    D.eventually_constant_and_detection_depth_tends_to_infinity := by
  constructor
  · intro N
    refine
      ⟨D.conclusion_bounded_depth_inseparability_under_cmv_freeze_stabilizationBound N,
        D.conclusion_bounded_depth_inseparability_under_cmv_freeze_certificate N
          (D.conclusion_bounded_depth_inseparability_under_cmv_freeze_limitWindow N), ?_⟩
    intro L hL
    rw [D.conclusion_bounded_depth_inseparability_under_cmv_freeze_window_stabilizes N L hL]
  · intro B
    refine
      ⟨D.conclusion_bounded_depth_inseparability_under_cmv_freeze_stabilizationBound B, ?_⟩
    intro L hL
    by_contra hnot
    have hdepth :
        D.conclusion_bounded_depth_inseparability_under_cmv_freeze_detectionDepth L ≤ B :=
      Nat.le_of_not_gt hnot
    have hdetect :
        D.conclusion_bounded_depth_inseparability_under_cmv_freeze_certificate B
          (D.conclusion_bounded_depth_inseparability_under_cmv_freeze_window B L) = true :=
      D.conclusion_bounded_depth_inseparability_under_cmv_freeze_detects_at_bounded_depth B L
        hdepth
    have hblind :
        D.conclusion_bounded_depth_inseparability_under_cmv_freeze_certificate B
          (D.conclusion_bounded_depth_inseparability_under_cmv_freeze_window B L) = false := by
      rw [D.conclusion_bounded_depth_inseparability_under_cmv_freeze_window_stabilizes B L hL]
      exact D.conclusion_bounded_depth_inseparability_under_cmv_freeze_limit_blind B
    rw [hblind] at hdetect
    cases hdetect

end Omega.Conclusion
