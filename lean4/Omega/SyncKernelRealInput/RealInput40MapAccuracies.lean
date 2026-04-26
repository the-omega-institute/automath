import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

namespace Omega.SyncKernelRealInput

noncomputable section

/-- The ten sync states that appear in the audited `20`-state joint table. -/
inductive real_input_40_map_accuracies_sync_state
  | s000
  | s001
  | s010
  | s01m1
  | s100
  | s11m1
  | s002
  | s101
  | s0m12
  | s1m12
  deriving DecidableEq

/-- The four memory states `m = (p_x, p_y)`. -/
inductive real_input_40_map_accuracies_memory_state
  | m00
  | m01
  | m10
  | m11
  deriving DecidableEq

/-- The audited joint law `P(s,m)` from the real-input-40 appendix. Unlisted pairs have mass `0`. -/
def real_input_40_map_accuracies_joint_mass :
    real_input_40_map_accuracies_sync_state →
      real_input_40_map_accuracies_memory_state → ℝ
  | .s000, .m00 => 1 / 20 + Real.sqrt 5 / 20
  | .s010, .m00 => 1 / 20 + Real.sqrt 5 / 20
  | .s001, .m00 => 3 / 20 - Real.sqrt 5 / 20
  | .s01m1, .m00 => 3 / 20 - Real.sqrt 5 / 20
  | .s100, .m00 => -1 / 20 + Real.sqrt 5 / 20
  | .s11m1, .m00 => -1 / 20 + Real.sqrt 5 / 20
  | .s000, .m01 => -11 / 20 + Real.sqrt 5 / 4
  | .s000, .m10 => -11 / 20 + Real.sqrt 5 / 4
  | .s001, .m01 => 3 / 10 - Real.sqrt 5 / 10
  | .s001, .m10 => 3 / 10 - Real.sqrt 5 / 10
  | .s002, .m01 => -1 / 5 + Real.sqrt 5 / 10
  | .s002, .m10 => -1 / 5 + Real.sqrt 5 / 10
  | .s100, .m01 => 1 / 2 - Real.sqrt 5 / 5
  | .s100, .m10 => 1 / 2 - Real.sqrt 5 / 5
  | .s101, .m01 => 3 / 20 - Real.sqrt 5 / 20
  | .s101, .m10 => 3 / 20 - Real.sqrt 5 / 20
  | .s0m12, .m11 => -1 / 5 + Real.sqrt 5 / 10
  | .s002, .m11 => -3 / 4 + 7 * Real.sqrt 5 / 20
  | .s1m12, .m11 => 7 / 20 - 3 * Real.sqrt 5 / 20
  | .s101, .m11 => 9 / 10 - 2 * Real.sqrt 5 / 5
  | _, _ => 0

/-- Statewise maximizing contribution for the four-way MAP estimator `M <- S`. -/
def real_input_40_map_accuracies_memory_contribution :
    real_input_40_map_accuracies_sync_state → ℝ
  | .s000 => real_input_40_map_accuracies_joint_mass .s000 .m00
  | .s001 => real_input_40_map_accuracies_joint_mass .s001 .m01
  | .s010 => real_input_40_map_accuracies_joint_mass .s010 .m00
  | .s01m1 => real_input_40_map_accuracies_joint_mass .s01m1 .m00
  | .s100 => real_input_40_map_accuracies_joint_mass .s100 .m00
  | .s11m1 => real_input_40_map_accuracies_joint_mass .s11m1 .m00
  | .s002 => real_input_40_map_accuracies_joint_mass .s002 .m11
  | .s101 => real_input_40_map_accuracies_joint_mass .s101 .m01
  | .s0m12 => real_input_40_map_accuracies_joint_mass .s0m12 .m11
  | .s1m12 => real_input_40_map_accuracies_joint_mass .s1m12 .m11

/-- Statewise maximizing contribution for decoding the bit `p_x`. -/
def real_input_40_map_accuracies_px_contribution :
    real_input_40_map_accuracies_sync_state → ℝ
  | .s000 =>
      real_input_40_map_accuracies_joint_mass .s000 .m00 +
        real_input_40_map_accuracies_joint_mass .s000 .m01
  | .s001 =>
      real_input_40_map_accuracies_joint_mass .s001 .m00 +
        real_input_40_map_accuracies_joint_mass .s001 .m01
  | .s010 => real_input_40_map_accuracies_joint_mass .s010 .m00
  | .s01m1 => real_input_40_map_accuracies_joint_mass .s01m1 .m00
  | .s100 =>
      real_input_40_map_accuracies_joint_mass .s100 .m00 +
        real_input_40_map_accuracies_joint_mass .s100 .m01
  | .s11m1 => real_input_40_map_accuracies_joint_mass .s11m1 .m00
  | .s002 =>
      real_input_40_map_accuracies_joint_mass .s002 .m10 +
        real_input_40_map_accuracies_joint_mass .s002 .m11
  | .s101 =>
      real_input_40_map_accuracies_joint_mass .s101 .m10 +
        real_input_40_map_accuracies_joint_mass .s101 .m11
  | .s0m12 => real_input_40_map_accuracies_joint_mass .s0m12 .m11
  | .s1m12 => real_input_40_map_accuracies_joint_mass .s1m12 .m11

/-- Statewise maximizing contribution for decoding the bit `p_y`. -/
def real_input_40_map_accuracies_py_contribution :
    real_input_40_map_accuracies_sync_state → ℝ
  | .s000 =>
      real_input_40_map_accuracies_joint_mass .s000 .m00 +
        real_input_40_map_accuracies_joint_mass .s000 .m10
  | .s001 =>
      real_input_40_map_accuracies_joint_mass .s001 .m00 +
        real_input_40_map_accuracies_joint_mass .s001 .m10
  | .s010 => real_input_40_map_accuracies_joint_mass .s010 .m00
  | .s01m1 => real_input_40_map_accuracies_joint_mass .s01m1 .m00
  | .s100 =>
      real_input_40_map_accuracies_joint_mass .s100 .m00 +
        real_input_40_map_accuracies_joint_mass .s100 .m10
  | .s11m1 => real_input_40_map_accuracies_joint_mass .s11m1 .m00
  | .s002 =>
      real_input_40_map_accuracies_joint_mass .s002 .m01 +
        real_input_40_map_accuracies_joint_mass .s002 .m11
  | .s101 =>
      real_input_40_map_accuracies_joint_mass .s101 .m01 +
        real_input_40_map_accuracies_joint_mass .s101 .m11
  | .s0m12 => real_input_40_map_accuracies_joint_mass .s0m12 .m11
  | .s1m12 => real_input_40_map_accuracies_joint_mass .s1m12 .m11

/-- Statewise maximizing contribution for decoding the collision indicator `C = 1_{m = 11}`. -/
def real_input_40_map_accuracies_collision_contribution :
    real_input_40_map_accuracies_sync_state → ℝ
  | .s000 =>
      real_input_40_map_accuracies_joint_mass .s000 .m00 +
        real_input_40_map_accuracies_joint_mass .s000 .m01 +
          real_input_40_map_accuracies_joint_mass .s000 .m10
  | .s001 =>
      real_input_40_map_accuracies_joint_mass .s001 .m00 +
        real_input_40_map_accuracies_joint_mass .s001 .m01 +
          real_input_40_map_accuracies_joint_mass .s001 .m10
  | .s010 => real_input_40_map_accuracies_joint_mass .s010 .m00
  | .s01m1 => real_input_40_map_accuracies_joint_mass .s01m1 .m00
  | .s100 =>
      real_input_40_map_accuracies_joint_mass .s100 .m00 +
        real_input_40_map_accuracies_joint_mass .s100 .m01 +
          real_input_40_map_accuracies_joint_mass .s100 .m10
  | .s11m1 => real_input_40_map_accuracies_joint_mass .s11m1 .m00
  | .s002 =>
      real_input_40_map_accuracies_joint_mass .s002 .m01 +
        real_input_40_map_accuracies_joint_mass .s002 .m10
  | .s101 =>
      real_input_40_map_accuracies_joint_mass .s101 .m01 +
        real_input_40_map_accuracies_joint_mass .s101 .m10
  | .s0m12 => real_input_40_map_accuracies_joint_mass .s0m12 .m11
  | .s1m12 => real_input_40_map_accuracies_joint_mass .s1m12 .m11

/-- Statewise maximizing contribution for decoding the parity `p_x xor p_y`. -/
def real_input_40_map_accuracies_xor_contribution :
    real_input_40_map_accuracies_sync_state → ℝ
  | .s000 => real_input_40_map_accuracies_joint_mass .s000 .m00
  | .s001 =>
      real_input_40_map_accuracies_joint_mass .s001 .m01 +
        real_input_40_map_accuracies_joint_mass .s001 .m10
  | .s010 => real_input_40_map_accuracies_joint_mass .s010 .m00
  | .s01m1 => real_input_40_map_accuracies_joint_mass .s01m1 .m00
  | .s100 =>
      real_input_40_map_accuracies_joint_mass .s100 .m01 +
        real_input_40_map_accuracies_joint_mass .s100 .m10
  | .s11m1 => real_input_40_map_accuracies_joint_mass .s11m1 .m00
  | .s002 =>
      real_input_40_map_accuracies_joint_mass .s002 .m01 +
        real_input_40_map_accuracies_joint_mass .s002 .m10
  | .s101 =>
      real_input_40_map_accuracies_joint_mass .s101 .m01 +
        real_input_40_map_accuracies_joint_mass .s101 .m10
  | .s0m12 => real_input_40_map_accuracies_joint_mass .s0m12 .m11
  | .s1m12 => real_input_40_map_accuracies_joint_mass .s1m12 .m11

/-- The four audited MAP accuracies from the state-by-state maximizers. -/
def real_input_40_map_accuracies_memory_accuracy : ℝ :=
  real_input_40_map_accuracies_memory_contribution .s000 +
    real_input_40_map_accuracies_memory_contribution .s001 +
    real_input_40_map_accuracies_memory_contribution .s010 +
    real_input_40_map_accuracies_memory_contribution .s01m1 +
    real_input_40_map_accuracies_memory_contribution .s100 +
    real_input_40_map_accuracies_memory_contribution .s11m1 +
    real_input_40_map_accuracies_memory_contribution .s002 +
    real_input_40_map_accuracies_memory_contribution .s101 +
    real_input_40_map_accuracies_memory_contribution .s0m12 +
    real_input_40_map_accuracies_memory_contribution .s1m12

def real_input_40_map_accuracies_px_accuracy : ℝ :=
  real_input_40_map_accuracies_px_contribution .s000 +
    real_input_40_map_accuracies_px_contribution .s001 +
    real_input_40_map_accuracies_px_contribution .s010 +
    real_input_40_map_accuracies_px_contribution .s01m1 +
    real_input_40_map_accuracies_px_contribution .s100 +
    real_input_40_map_accuracies_px_contribution .s11m1 +
    real_input_40_map_accuracies_px_contribution .s002 +
    real_input_40_map_accuracies_px_contribution .s101 +
    real_input_40_map_accuracies_px_contribution .s0m12 +
    real_input_40_map_accuracies_px_contribution .s1m12

def real_input_40_map_accuracies_py_accuracy : ℝ :=
  real_input_40_map_accuracies_py_contribution .s000 +
    real_input_40_map_accuracies_py_contribution .s001 +
    real_input_40_map_accuracies_py_contribution .s010 +
    real_input_40_map_accuracies_py_contribution .s01m1 +
    real_input_40_map_accuracies_py_contribution .s100 +
    real_input_40_map_accuracies_py_contribution .s11m1 +
    real_input_40_map_accuracies_py_contribution .s002 +
    real_input_40_map_accuracies_py_contribution .s101 +
    real_input_40_map_accuracies_py_contribution .s0m12 +
    real_input_40_map_accuracies_py_contribution .s1m12

def real_input_40_map_accuracies_collision_accuracy : ℝ :=
  real_input_40_map_accuracies_collision_contribution .s000 +
    real_input_40_map_accuracies_collision_contribution .s001 +
    real_input_40_map_accuracies_collision_contribution .s010 +
    real_input_40_map_accuracies_collision_contribution .s01m1 +
    real_input_40_map_accuracies_collision_contribution .s100 +
    real_input_40_map_accuracies_collision_contribution .s11m1 +
    real_input_40_map_accuracies_collision_contribution .s002 +
    real_input_40_map_accuracies_collision_contribution .s101 +
    real_input_40_map_accuracies_collision_contribution .s0m12 +
    real_input_40_map_accuracies_collision_contribution .s1m12

def real_input_40_map_accuracies_xor_accuracy : ℝ :=
  real_input_40_map_accuracies_xor_contribution .s000 +
    real_input_40_map_accuracies_xor_contribution .s001 +
    real_input_40_map_accuracies_xor_contribution .s010 +
    real_input_40_map_accuracies_xor_contribution .s01m1 +
    real_input_40_map_accuracies_xor_contribution .s100 +
    real_input_40_map_accuracies_xor_contribution .s11m1 +
    real_input_40_map_accuracies_xor_contribution .s002 +
    real_input_40_map_accuracies_xor_contribution .s101 +
    real_input_40_map_accuracies_xor_contribution .s0m12 +
    real_input_40_map_accuracies_xor_contribution .s1m12

def real_input_40_map_accuracies_statement : Prop :=
  real_input_40_map_accuracies_memory_accuracy = 3 * Real.sqrt 5 / 10 ∧
    real_input_40_map_accuracies_px_accuracy = 4 / 5 ∧
    real_input_40_map_accuracies_py_accuracy = 4 / 5 ∧
    real_input_40_map_accuracies_collision_accuracy = (17 + Real.sqrt 5) / 20 ∧
    real_input_40_map_accuracies_xor_accuracy = (37 - 9 * Real.sqrt 5) / 20

/-- Paper label: `prop:real-input-40-map-accuracies`. The audited joint table determines the
statewise MAP decision for the four-way memory variable and for the listed binary observables. -/
theorem paper_real_input_40_map_accuracies :
    real_input_40_map_accuracies_statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold real_input_40_map_accuracies_memory_accuracy
      real_input_40_map_accuracies_memory_contribution
      real_input_40_map_accuracies_joint_mass
    ring_nf
  · unfold real_input_40_map_accuracies_px_accuracy
      real_input_40_map_accuracies_px_contribution
      real_input_40_map_accuracies_joint_mass
    ring_nf
  · unfold real_input_40_map_accuracies_py_accuracy
      real_input_40_map_accuracies_py_contribution
      real_input_40_map_accuracies_joint_mass
    ring_nf
  · unfold real_input_40_map_accuracies_collision_accuracy
      real_input_40_map_accuracies_collision_contribution
      real_input_40_map_accuracies_joint_mass
    ring_nf
  · unfold real_input_40_map_accuracies_xor_accuracy
      real_input_40_map_accuracies_xor_contribution
      real_input_40_map_accuracies_joint_mass
    ring_nf

end

end Omega.SyncKernelRealInput
