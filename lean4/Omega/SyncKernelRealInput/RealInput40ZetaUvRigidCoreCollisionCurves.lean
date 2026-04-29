import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic
import Omega.SyncKernelRealInput.RealInput40ZetaUvSqrtvEigs

namespace Omega.SyncKernelRealInput

noncomputable section

/-- Positive rigid/core collision locus after the substitution `z = 1 / sqrt(v)`. -/
def real_input_40_zeta_uv_rigid_core_collision_curves_Cplus : Set (ℝ × ℝ) :=
  {p | 0 < p.1 ∧ 0 < p.2 ∧ p.1 = 1 / real_input_40_zeta_uv_sqrtv_eigs_root_pos p.2}

/-- Negative rigid/core collision locus after the substitution `z = -1 / sqrt(v)`. -/
def real_input_40_zeta_uv_rigid_core_collision_curves_Cminus : Set (ℝ × ℝ) :=
  {p | 0 < p.1 ∧ 0 < p.2 ∧ p.1 = -real_input_40_zeta_uv_sqrtv_eigs_root_neg p.2}

/-- Paper label: `thm:real-input-40-zeta-uv-rigid-core-collision-curves`. The rigid roots
`z = ±1 / sqrt(v)` yield the explicit positive-region collision curves `u = sqrt(v)` and
`u = 1 / sqrt(v)`, and their only simultaneous collision is `(u, v) = (1, 1)`. -/
theorem paper_real_input_40_zeta_uv_rigid_core_collision_curves (u v : ℝ) (hv : 0 < v) :
    (u - 1 / real_input_40_zeta_uv_sqrtv_eigs_root_pos v = u - Real.sqrt v) ∧
      (u + real_input_40_zeta_uv_sqrtv_eigs_root_neg v = u - (Real.sqrt v)⁻¹) ∧
      ((u, v) ∈ real_input_40_zeta_uv_rigid_core_collision_curves_Cplus ↔
        0 < u ∧ u = Real.sqrt v) ∧
      ((u, v) ∈ real_input_40_zeta_uv_rigid_core_collision_curves_Cminus ↔
        0 < u ∧ u = (Real.sqrt v)⁻¹) ∧
      (((u, v) ∈ real_input_40_zeta_uv_rigid_core_collision_curves_Cplus ∧
          (u, v) ∈ real_input_40_zeta_uv_rigid_core_collision_curves_Cminus) ↔
        u = 1 ∧ v = 1) := by
  rcases paper_real_input_40_zeta_uv_sqrtv_eigs v hv with
    ⟨_, _, hrootPos, _, _⟩
  have hsqrt_pos : 0 < Real.sqrt v := Real.sqrt_pos.2 hv
  have hsqrt_ne : Real.sqrt v ≠ 0 := ne_of_gt hsqrt_pos
  have hCplus :
      ((u, v) ∈ real_input_40_zeta_uv_rigid_core_collision_curves_Cplus ↔
        0 < u ∧ u = Real.sqrt v) := by
    constructor
    · intro h
      rcases h with ⟨hu, _, huEq⟩
      refine ⟨hu, ?_⟩
      simpa [hrootPos] using huEq
    · rintro ⟨hu, rfl⟩
      refine ⟨hu, hv, ?_⟩
      simpa [hrootPos]
  have hCminus :
      ((u, v) ∈ real_input_40_zeta_uv_rigid_core_collision_curves_Cminus ↔
        0 < u ∧ u = (Real.sqrt v)⁻¹) := by
    constructor
    · intro h
      rcases h with ⟨hu, _, huEq⟩
      refine ⟨hu, ?_⟩
      simpa [real_input_40_zeta_uv_sqrtv_eigs_root_neg] using huEq
    · rintro ⟨hu, rfl⟩
      refine ⟨hu, hv, ?_⟩
      simp [real_input_40_zeta_uv_sqrtv_eigs_root_neg]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [hrootPos]
  · simpa [sub_eq_add_neg, real_input_40_zeta_uv_sqrtv_eigs_root_neg]
  · exact hCplus
  · exact hCminus
  · constructor
    · rintro ⟨hplus, hminus⟩
      have hu_plus : u = Real.sqrt v := (hCplus.mp hplus).2
      have hu_minus : u = (Real.sqrt v)⁻¹ := (hCminus.mp hminus).2
      have hsqrt_eq_inv : Real.sqrt v = (Real.sqrt v)⁻¹ := by
        linarith
      have hsq_one : Real.sqrt v * Real.sqrt v = 1 := by
        have hmul := congrArg (fun x : ℝ => x * Real.sqrt v) hsqrt_eq_inv
        simpa [hsqrt_ne] using hmul
      have hsqrt_one : Real.sqrt v = 1 := by
        nlinarith
      have hu_one : u = 1 := by
        nlinarith [hu_plus, hsqrt_one]
      have hv_one : v = 1 := by
        nlinarith [Real.sq_sqrt (le_of_lt hv), hsqrt_one]
      exact ⟨hu_one, hv_one⟩
    · rintro ⟨rfl, rfl⟩
      constructor
      · refine ⟨by norm_num, by norm_num, ?_⟩
        simp [real_input_40_zeta_uv_sqrtv_eigs_root_pos]
      · refine ⟨by norm_num, by norm_num, ?_⟩
        simp [real_input_40_zeta_uv_sqrtv_eigs_root_neg]

end

end Omega.SyncKernelRealInput
