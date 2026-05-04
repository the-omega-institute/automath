import Mathlib.Tactic

namespace Omega.Zeta

/-- The inverse golden-ratio scale used by the two-cycle Abel finite-part shift. -/
noncomputable def xi_time_part73_two_cycle_abel_finitepart_shift_phi_inv : ℝ :=
  (Real.sqrt 5 - 1) / 2

/-- The fourth inverse golden-ratio power, written in the normalization of the paper. -/
noncomputable def xi_time_part73_two_cycle_abel_finitepart_shift_phi_inv_four : ℝ :=
  xi_time_part73_two_cycle_abel_finitepart_shift_phi_inv ^ 4

/-- Concrete data for the primitive-core split and Abel finite-part normalization. -/
structure xi_time_part73_two_cycle_abel_finitepart_shift_Data where
  z : ℝ
  zstar : ℝ
  primitive : ℝ → ℝ
  core : ℝ → ℝ
  logM : ℝ
  logMcore : ℝ
  M : ℝ
  Mcore : ℝ
  primitive_core_split : ∀ z, primitive z = z ^ 2 + core z
  zstar_eq : zstar = xi_time_part73_two_cycle_abel_finitepart_shift_phi_inv ^ 2
  abel_finite_part_shift : logM = logMcore + zstar ^ 2
  M_eq_exp : M = Real.exp logM
  Mcore_eq_exp : Mcore = Real.exp logMcore

/-- Paper-facing statement for the exact two-cycle Abel finite-part shift. -/
def xi_time_part73_two_cycle_abel_finitepart_shift_statement
    (D : xi_time_part73_two_cycle_abel_finitepart_shift_Data) : Prop :=
  D.core D.z = D.primitive D.z - D.z ^ 2 ∧
    D.zstar ^ 2 = xi_time_part73_two_cycle_abel_finitepart_shift_phi_inv_four ∧
    D.logM - D.logMcore = xi_time_part73_two_cycle_abel_finitepart_shift_phi_inv_four ∧
    xi_time_part73_two_cycle_abel_finitepart_shift_phi_inv_four =
      (7 - 3 * Real.sqrt 5) / 2 ∧
    D.Mcore =
      Real.exp (-xi_time_part73_two_cycle_abel_finitepart_shift_phi_inv_four) * D.M

lemma xi_time_part73_two_cycle_abel_finitepart_shift_phi_inv_four_closed :
    xi_time_part73_two_cycle_abel_finitepart_shift_phi_inv_four =
      (7 - 3 * Real.sqrt 5) / 2 := by
  let x : ℝ := Real.sqrt 5
  have hx2 : x ^ 2 = (5 : ℝ) := by
    dsimp [x]
    rw [Real.sq_sqrt]
    norm_num
  have hx3 : x ^ 3 = 5 * x := by
    calc
      x ^ 3 = x * x ^ 2 := by ring
      _ = 5 * x := by rw [hx2]; ring
  have hx4 : x ^ 4 = 25 := by
    calc
      x ^ 4 = (x ^ 2) ^ 2 := by ring
      _ = 25 := by rw [hx2]; norm_num
  unfold xi_time_part73_two_cycle_abel_finitepart_shift_phi_inv_four
    xi_time_part73_two_cycle_abel_finitepart_shift_phi_inv
  change ((x - 1) / 2) ^ 4 = (7 - 3 * x) / 2
  calc
    ((x - 1) / 2) ^ 4 = (x ^ 4 - 4 * x ^ 3 + 6 * x ^ 2 - 4 * x + 1) / 16 := by
      ring
    _ = (7 - 3 * x) / 2 := by
      rw [hx4, hx3, hx2]
      ring

/-- Paper label: `thm:xi-time-part73-two-cycle-abel-finitepart-shift`. -/
theorem paper_xi_time_part73_two_cycle_abel_finitepart_shift
    (D : xi_time_part73_two_cycle_abel_finitepart_shift_Data) :
    xi_time_part73_two_cycle_abel_finitepart_shift_statement D := by
  have hcore : D.core D.z = D.primitive D.z - D.z ^ 2 := by
    have hsplit := D.primitive_core_split D.z
    linarith
  have hzstar_sq :
      D.zstar ^ 2 = xi_time_part73_two_cycle_abel_finitepart_shift_phi_inv_four := by
    rw [D.zstar_eq, xi_time_part73_two_cycle_abel_finitepart_shift_phi_inv_four]
    ring
  have hlog :
      D.logM - D.logMcore =
        xi_time_part73_two_cycle_abel_finitepart_shift_phi_inv_four := by
    linarith [D.abel_finite_part_shift, hzstar_sq]
  have hMcore :
      D.Mcore =
        Real.exp (-xi_time_part73_two_cycle_abel_finitepart_shift_phi_inv_four) * D.M := by
    rw [D.Mcore_eq_exp, D.M_eq_exp]
    have hlogM :
        D.logM =
          D.logMcore + xi_time_part73_two_cycle_abel_finitepart_shift_phi_inv_four := by
      linarith [D.abel_finite_part_shift, hzstar_sq]
    calc
      Real.exp D.logMcore =
          Real.exp (-xi_time_part73_two_cycle_abel_finitepart_shift_phi_inv_four + D.logM) := by
            rw [hlogM]
            ring_nf
      _ =
          Real.exp (-xi_time_part73_two_cycle_abel_finitepart_shift_phi_inv_four) *
            Real.exp D.logM := by
            rw [Real.exp_add]
  exact ⟨hcore, hzstar_sq, hlog,
    xi_time_part73_two_cycle_abel_finitepart_shift_phi_inv_four_closed, hMcore⟩

end Omega.Zeta
