import Omega.Zeta.XiTimePart9zeCenterCondexpPimsnerPopaIndex

namespace Omega.Zeta

/-- The window-`6` Jones-ray obstruction constant for a fiber of degree `d`. -/
def xi_time_part9ze_window6_jones_ray_maxshell_localization_blockConstant
    (d : ℕ) : ℚ :=
  1 / (d : ℚ)

/-- The concrete max-shell localization statement over the audited window-`6` table. -/
def xi_time_part9ze_window6_jones_ray_maxshell_localization_statement : Prop :=
  (∀ lambda : ℚ,
    1 / 4 < lambda →
      ∃ i : Fin 21,
        xi_time_part9ze_center_condexp_pimsner_popa_index_window6FiberDegree i = 4 ∧
          ¬ lambda ≤
            xi_time_part9ze_window6_jones_ray_maxshell_localization_blockConstant 4) ∧
    (∀ i : Fin 21,
      xi_time_part9ze_center_condexp_pimsner_popa_index_window6FiberDegree i = 2 ∨
        xi_time_part9ze_center_condexp_pimsner_popa_index_window6FiberDegree i = 3 →
          1 / 3 ≤
            xi_time_part9ze_window6_jones_ray_maxshell_localization_blockConstant
              (xi_time_part9ze_center_condexp_pimsner_popa_index_window6FiberDegree i)) ∧
      ((Finset.univ.filter fun i : Fin 21 =>
          xi_time_part9ze_center_condexp_pimsner_popa_index_window6FiberDegree i = 4).card = 9)

/-- Paper label: `prop:xi-time-part9ze-window6-jones-ray-maxshell-localization`. -/
theorem paper_xi_time_part9ze_window6_jones_ray_maxshell_localization :
    xi_time_part9ze_window6_jones_ray_maxshell_localization_statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro lambda hlambda
    refine ⟨⟨12, by norm_num⟩, ?_, ?_⟩
    · norm_num [xi_time_part9ze_center_condexp_pimsner_popa_index_window6FiberDegree]
    · simpa [xi_time_part9ze_window6_jones_ray_maxshell_localization_blockConstant]
        using not_le_of_gt hlambda
  · intro i hi
    rcases hi with hi | hi
    · rw [hi]
      norm_num [xi_time_part9ze_window6_jones_ray_maxshell_localization_blockConstant]
    · rw [hi]
      norm_num [xi_time_part9ze_window6_jones_ray_maxshell_localization_blockConstant]
  · native_decide

end Omega.Zeta
