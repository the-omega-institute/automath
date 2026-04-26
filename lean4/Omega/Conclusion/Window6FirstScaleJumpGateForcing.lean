import Mathlib.Tactic

namespace Omega.Conclusion

def conclusion_window6_first_scale_jump_gate_forcing_boundary_fiber_size : ℕ → ℕ
  | 6 => 2
  | 7 => 3
  | 8 => 3
  | _ => 0

def conclusion_window6_first_scale_jump_gate_forcing_faithful_binary_readout (m B : ℕ) : Prop :=
  conclusion_window6_first_scale_jump_gate_forcing_boundary_fiber_size m ≤ 2 ^ B

def conclusion_window6_first_scale_jump_gate_forcing_Bmin (m : ℕ) : ℕ :=
  Nat.clog 2 (conclusion_window6_first_scale_jump_gate_forcing_boundary_fiber_size m)

/-- Paper label: `thm:conclusion-window6-first-scale-jump-gate-forcing`. -/
theorem paper_conclusion_window6_first_scale_jump_gate_forcing :
    conclusion_window6_first_scale_jump_gate_forcing_boundary_fiber_size 6 = 2 ∧
      conclusion_window6_first_scale_jump_gate_forcing_boundary_fiber_size 7 = 3 ∧
      conclusion_window6_first_scale_jump_gate_forcing_boundary_fiber_size 8 = 3 ∧
      conclusion_window6_first_scale_jump_gate_forcing_faithful_binary_readout 6 1 ∧
      ¬ conclusion_window6_first_scale_jump_gate_forcing_faithful_binary_readout 7 1 ∧
      ¬ conclusion_window6_first_scale_jump_gate_forcing_faithful_binary_readout 8 1 ∧
      conclusion_window6_first_scale_jump_gate_forcing_Bmin 6 = 1 ∧
      2 ≤ conclusion_window6_first_scale_jump_gate_forcing_Bmin 7 ∧
      2 ≤ conclusion_window6_first_scale_jump_gate_forcing_Bmin 8 := by
  simp [conclusion_window6_first_scale_jump_gate_forcing_faithful_binary_readout,
    conclusion_window6_first_scale_jump_gate_forcing_Bmin,
    conclusion_window6_first_scale_jump_gate_forcing_boundary_fiber_size]
  native_decide

end Omega.Conclusion
