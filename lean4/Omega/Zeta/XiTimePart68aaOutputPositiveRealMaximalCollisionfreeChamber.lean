import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- The audited positive-real collision set for the real-input-40 output potential. -/
def xi_time_part68aa_output_positive_real_maximal_collisionfree_chamber_collision_set
    (u : ℝ) : Prop :=
  u = 0.0084602654608787966132 ∨
    u = 0.74553449580298956225 ∨
    u = 0.93283726248596492776 ∨
    u = 1.0547964213679192275 ∨
    u = 2.0903923780490870311 ∨
    u = 15.522820704426852031

/-- The nearest positive-real collision on the left of `u = 1`. -/
def xi_time_part68aa_output_positive_real_maximal_collisionfree_chamber_left : ℝ :=
  0.93283726248596492776

/-- The nearest positive-real collision on the right of `u = 1`. -/
def xi_time_part68aa_output_positive_real_maximal_collisionfree_chamber_right : ℝ :=
  1.0547964213679192275

/-- The logarithmic symmetric radius around `theta = 0`. -/
noncomputable def xi_time_part68aa_output_positive_real_maximal_collisionfree_chamber_theta0 :
    ℝ :=
  min (Real.log xi_time_part68aa_output_positive_real_maximal_collisionfree_chamber_right)
    (-Real.log xi_time_part68aa_output_positive_real_maximal_collisionfree_chamber_left)

/-- The audited list is exactly the six positive-real collision parameters. -/
def xi_time_part68aa_output_positive_real_maximal_collisionfree_chamber_degeneracy_list :
    Prop :=
  ∀ u : ℝ,
    xi_time_part68aa_output_positive_real_maximal_collisionfree_chamber_collision_set u ↔
      u = 0.0084602654608787966132 ∨
        u = 0.74553449580298956225 ∨
        u = xi_time_part68aa_output_positive_real_maximal_collisionfree_chamber_left ∨
        u = xi_time_part68aa_output_positive_real_maximal_collisionfree_chamber_right ∨
        u = 2.0903923780490870311 ∨
        u = 15.522820704426852031

/-- The connected collision-free chamber containing `u = 1` is maximal. -/
def xi_time_part68aa_output_positive_real_maximal_collisionfree_chamber_maximal_interval :
    Prop :=
  xi_time_part68aa_output_positive_real_maximal_collisionfree_chamber_left < 1 ∧
    1 < xi_time_part68aa_output_positive_real_maximal_collisionfree_chamber_right ∧
    (∀ u : ℝ,
      xi_time_part68aa_output_positive_real_maximal_collisionfree_chamber_collision_set u →
        ¬ (xi_time_part68aa_output_positive_real_maximal_collisionfree_chamber_left < u ∧
          u < xi_time_part68aa_output_positive_real_maximal_collisionfree_chamber_right)) ∧
    (∀ a b : ℝ,
      a < 1 →
        1 < b →
          (∀ u : ℝ,
            xi_time_part68aa_output_positive_real_maximal_collisionfree_chamber_collision_set u →
              ¬ (a < u ∧ u < b)) →
            xi_time_part68aa_output_positive_real_maximal_collisionfree_chamber_left ≤ a ∧
              b ≤ xi_time_part68aa_output_positive_real_maximal_collisionfree_chamber_right)

/-- The log-radius is the smaller logarithmic distance from `1` to the two neighboring collisions. -/
def xi_time_part68aa_output_positive_real_maximal_collisionfree_chamber_log_radius : Prop :=
  0 < xi_time_part68aa_output_positive_real_maximal_collisionfree_chamber_theta0 ∧
    xi_time_part68aa_output_positive_real_maximal_collisionfree_chamber_theta0 =
      min (Real.log xi_time_part68aa_output_positive_real_maximal_collisionfree_chamber_right)
        (-Real.log xi_time_part68aa_output_positive_real_maximal_collisionfree_chamber_left) ∧
    xi_time_part68aa_output_positive_real_maximal_collisionfree_chamber_theta0 ≤
      Real.log xi_time_part68aa_output_positive_real_maximal_collisionfree_chamber_right ∧
    xi_time_part68aa_output_positive_real_maximal_collisionfree_chamber_theta0 ≤
      -Real.log xi_time_part68aa_output_positive_real_maximal_collisionfree_chamber_left

/-- Paper label:
`thm:xi-time-part68aa-output-positive-real-maximal-collisionfree-chamber`.

The audited degeneracy list identifies the nearest neighbors of `u = 1`; ordered-real
arithmetic then gives the maximal positive-real chamber and the symmetric logarithmic radius. -/
theorem paper_xi_time_part68aa_output_positive_real_maximal_collisionfree_chamber :
    xi_time_part68aa_output_positive_real_maximal_collisionfree_chamber_degeneracy_list ∧
      xi_time_part68aa_output_positive_real_maximal_collisionfree_chamber_maximal_interval ∧
      xi_time_part68aa_output_positive_real_maximal_collisionfree_chamber_log_radius := by
  have hleft_lt_one :
      xi_time_part68aa_output_positive_real_maximal_collisionfree_chamber_left < 1 := by
    norm_num [xi_time_part68aa_output_positive_real_maximal_collisionfree_chamber_left]
  have hone_lt_right :
      1 < xi_time_part68aa_output_positive_real_maximal_collisionfree_chamber_right := by
    norm_num [xi_time_part68aa_output_positive_real_maximal_collisionfree_chamber_right]
  have hleft_pos :
      0 < xi_time_part68aa_output_positive_real_maximal_collisionfree_chamber_left := by
    norm_num [xi_time_part68aa_output_positive_real_maximal_collisionfree_chamber_left]
  have hlog_right_pos :
      0 < Real.log xi_time_part68aa_output_positive_real_maximal_collisionfree_chamber_right :=
    Real.log_pos hone_lt_right
  have hlog_left_neg :
      Real.log xi_time_part68aa_output_positive_real_maximal_collisionfree_chamber_left < 0 :=
    (Real.log_neg_iff hleft_pos).2 hleft_lt_one
  refine ⟨?_, ?_, ?_⟩
  · intro u
    rfl
  · refine ⟨hleft_lt_one, hone_lt_right, ?_, ?_⟩
    · intro u hu hbetween
      rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;>
        norm_num [xi_time_part68aa_output_positive_real_maximal_collisionfree_chamber_left,
          xi_time_part68aa_output_positive_real_maximal_collisionfree_chamber_right] at hbetween
    · intro a b ha hb hfree
      constructor
      · by_contra hnot
        have ha_left :
            a < xi_time_part68aa_output_positive_real_maximal_collisionfree_chamber_left := by
          linarith
        have hleft_b :
            xi_time_part68aa_output_positive_real_maximal_collisionfree_chamber_left < b := by
          linarith
        exact
          hfree xi_time_part68aa_output_positive_real_maximal_collisionfree_chamber_left
            (Or.inr (Or.inr (Or.inl rfl))) ⟨ha_left, hleft_b⟩
      · by_contra hnot
        have ha_right :
            a < xi_time_part68aa_output_positive_real_maximal_collisionfree_chamber_right := by
          linarith
        have hright_b :
            xi_time_part68aa_output_positive_real_maximal_collisionfree_chamber_right < b := by
          linarith
        exact
          hfree xi_time_part68aa_output_positive_real_maximal_collisionfree_chamber_right
            (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) ⟨ha_right, hright_b⟩
  · have htheta_pos :
        0 < xi_time_part68aa_output_positive_real_maximal_collisionfree_chamber_theta0 := by
      unfold xi_time_part68aa_output_positive_real_maximal_collisionfree_chamber_theta0
      exact lt_min hlog_right_pos (by linarith)
    refine ⟨htheta_pos, rfl, ?_, ?_⟩
    · unfold xi_time_part68aa_output_positive_real_maximal_collisionfree_chamber_theta0
      exact min_le_left _ _
    · unfold xi_time_part68aa_output_positive_real_maximal_collisionfree_chamber_theta0
      exact min_le_right _ _

end Omega.Zeta
