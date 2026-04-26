import Omega.Conclusion.ScreenLinearReadoutNullTrichotomyCollapse
import Omega.SPG.ScreenKernelConnectedComponents
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Stepwise monotonicity along a screen chain upgrades to the expected antitone comparison. -/
lemma conclusion_screen_delayed_observation_geometric_decision_time_antitone
    (components : ℕ → ℕ) (hmono : ∀ t, components (t + 1) ≤ components t) :
    ∀ ⦃s t : ℕ⦄, s ≤ t → components t ≤ components s := by
  intro s t hst
  induction t, hst using Nat.le_induction with
  | base =>
      simp
  | succ t hst ih =>
      exact le_trans (hmono t) ih

/-- Paper-facing delayed-observation decision-time wrapper. Along a monotone screen chain, the
readout on the visible image is total exactly when the screen graph is connected; before the
decision threshold the same readout is collision-null with fiber size `2^(c-1)`, and once the
chain reaches the connected regime the uniqueness persists for all later times. -/
def conclusion_screen_delayed_observation_geometric_decision_time_statement : Prop :=
  ∀ (components : ℕ → ℕ) (threshold : ℕ),
    (∀ t, 1 ≤ components t) →
    (∀ t, components (t + 1) ≤ components t) →
        (∀ t,
          conclusion_screen_linear_readout_null_trichotomy_collapse_readout true
              (2 ^ (components t - 1)) =
            conclusion_screen_linear_readout_null_trichotomy_collapse_status.Tot ↔
            components t = 1) ∧
        (∀ t < threshold,
          conclusion_screen_linear_readout_null_trichotomy_collapse_readout true
              (2 ^ (components t - 1)) =
            conclusion_screen_linear_readout_null_trichotomy_collapse_status.CollNULL ↔
            1 < components t) ∧
        (components threshold = 1 →
          ∀ t, threshold ≤ t →
            conclusion_screen_linear_readout_null_trichotomy_collapse_readout true
                (2 ^ (components t - 1)) =
              conclusion_screen_linear_readout_null_trichotomy_collapse_status.Tot ∧
              components t = 1)

/-- The image-side readout is collision-null exactly when the connected-component count exceeds
`1`; the threshold parameter is irrelevant for this pointwise criterion. -/
lemma conclusion_screen_delayed_observation_geometric_decision_time_collnull_iff
    (components : ℕ → ℕ) (t : ℕ) :
    conclusion_screen_linear_readout_null_trichotomy_collapse_readout true
        (2 ^ (components t - 1)) =
      conclusion_screen_linear_readout_null_trichotomy_collapse_status.CollNULL ↔
      1 < components t := by
  have hcollapse :=
    paper_conclusion_screen_linear_readout_null_trichotomy_collapse 0 0 (components t - 1)
  have hiff : 0 < components t - 1 ↔ 1 < components t := by
    omega
  exact hcollapse.2.1.trans hiff

/-- The collision-null criterion is pointwise, so any pre-threshold time inherits the same
equivalence. -/
lemma conclusion_screen_delayed_observation_geometric_decision_time_collnull_before_threshold
    (components : ℕ → ℕ) (threshold t : ℕ) (_ht : t < threshold) :
    conclusion_screen_linear_readout_null_trichotomy_collapse_readout true
        (2 ^ (components t - 1)) =
      conclusion_screen_linear_readout_null_trichotomy_collapse_status.CollNULL ↔
      1 < components t :=
  conclusion_screen_delayed_observation_geometric_decision_time_collnull_iff components t

/-- Paper label: `thm:conclusion-screen-delayed-observation-geometric-decision-time`. -/
theorem paper_conclusion_screen_delayed_observation_geometric_decision_time :
    conclusion_screen_delayed_observation_geometric_decision_time_statement := by
  intro components threshold hpos hmono
  refine ⟨
    (fun t => by
      have hcollapse :=
        paper_conclusion_screen_linear_readout_null_trichotomy_collapse 0 0 (components t - 1)
      have hc_pos : 0 < components t := lt_of_lt_of_le (by decide : 0 < 1) (hpos t)
      have hkernel :
          components t - 1 = 0 ↔ components t = 1 :=
        Omega.SPG.ScreenKernelConnectedComponents.kernel_dim_eq_components_minus_one
          (components t) hc_pos
      exact hcollapse.2.2.1.trans hkernel),
    (show ∀ t < threshold,
        conclusion_screen_linear_readout_null_trichotomy_collapse_readout true
            (2 ^ (components t - 1)) =
          conclusion_screen_linear_readout_null_trichotomy_collapse_status.CollNULL ↔
          1 < components t from
      fun t ht =>
        conclusion_screen_delayed_observation_geometric_decision_time_collnull_before_threshold
          components threshold t ht),
    ?_⟩
  intro hthreshold t htt
  have hchain :
      components t ≤ components threshold :=
    conclusion_screen_delayed_observation_geometric_decision_time_antitone components hmono htt
  have hkernel_mono :
      components t - 1 ≤ components threshold - 1 :=
    Omega.SPG.ScreenKernelConnectedComponents.screen_monotone_kernel
      (components threshold) (components t)
      (lt_of_lt_of_le (by decide : 0 < 1) (hpos threshold))
      (lt_of_lt_of_le (by decide : 0 < 1) (hpos t))
      hchain
  have hkernel_zero : components t - 1 = 0 := by
    rw [hthreshold] at hkernel_mono
    omega
  have hcomp_one : components t = 1 := by
    have hc_pos : 0 < components t := lt_of_lt_of_le (by decide : 0 < 1) (hpos t)
    exact
      (Omega.SPG.ScreenKernelConnectedComponents.kernel_dim_eq_components_minus_one
        (components t) hc_pos).mp hkernel_zero
  have hcollapse :=
    paper_conclusion_screen_linear_readout_null_trichotomy_collapse 0 0 (components t - 1)
  have hc_pos : 0 < components t := lt_of_lt_of_le (by decide : 0 < 1) (hpos t)
  have htot :
      conclusion_screen_linear_readout_null_trichotomy_collapse_readout true
          (2 ^ (components t - 1)) =
        conclusion_screen_linear_readout_null_trichotomy_collapse_status.Tot := by
    exact
      (hcollapse.2.2.1.trans
        (Omega.SPG.ScreenKernelConnectedComponents.kernel_dim_eq_components_minus_one
          (components t) hc_pos)).2 hcomp_one
  exact ⟨htot, hcomp_one⟩

end Omega.Conclusion
