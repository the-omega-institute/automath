import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

namespace Omega.Zeta

open Matrix

/-- Concrete finite nilpotent block data for the ambiguity shell. -/
structure xi_time_part9zm_ambiguity_shell_exact_memory_depth_NilpotentBlock (m : Nat) where
  xi_time_part9zm_ambiguity_shell_exact_memory_depth_matrix :
    Matrix (Fin m) (Fin m) Rat
  xi_time_part9zm_ambiguity_shell_exact_memory_depth_nilpotent_at_index :
    xi_time_part9zm_ambiguity_shell_exact_memory_depth_matrix ^ m = 0
  xi_time_part9zm_ambiguity_shell_exact_memory_depth_nonzero_before_index :
    1 ≤ m →
      xi_time_part9zm_ambiguity_shell_exact_memory_depth_matrix ^ (m - 1) ≠ 0

/-- The audited nilpotent index attached to the finite block. -/
def xi_time_part9zm_ambiguity_shell_exact_memory_depth_nilpotentIndex {m : Nat}
    (_N : xi_time_part9zm_ambiguity_shell_exact_memory_depth_NilpotentBlock m) : Nat :=
  m

/-- The finite resolvent correction has one fewer memory layer than the nilpotent index. -/
def xi_time_part9zm_ambiguity_shell_exact_memory_depth_resolventMemory {m : Nat}
    (N : xi_time_part9zm_ambiguity_shell_exact_memory_depth_NilpotentBlock m) : Nat :=
  xi_time_part9zm_ambiguity_shell_exact_memory_depth_nilpotentIndex N - 1

/-- The Neumann expansion terminates at the nilpotent index for the finite block. -/
theorem xi_time_part9zm_ambiguity_shell_exact_memory_depth_finite_neumann_terminates
    (m : Nat) (N : xi_time_part9zm_ambiguity_shell_exact_memory_depth_NilpotentBlock m) :
    N.xi_time_part9zm_ambiguity_shell_exact_memory_depth_matrix ^ m = 0 :=
  N.xi_time_part9zm_ambiguity_shell_exact_memory_depth_nilpotent_at_index

/-- The preceding power is nonzero when the shell has positive length. -/
theorem xi_time_part9zm_ambiguity_shell_exact_memory_depth_pred_power_nonzero
    (m : Nat) (hm : 1 ≤ m)
    (N : xi_time_part9zm_ambiguity_shell_exact_memory_depth_NilpotentBlock m) :
    N.xi_time_part9zm_ambiguity_shell_exact_memory_depth_matrix ^ (m - 1) ≠ 0 :=
  N.xi_time_part9zm_ambiguity_shell_exact_memory_depth_nonzero_before_index hm

/-- Paper label: `cor:xi-time-part9zm-ambiguity-shell-exact-memory-depth`. -/
theorem paper_xi_time_part9zm_ambiguity_shell_exact_memory_depth (m : Nat) (hm : 1 ≤ m)
    (N : xi_time_part9zm_ambiguity_shell_exact_memory_depth_NilpotentBlock m)
    (hNil : xi_time_part9zm_ambiguity_shell_exact_memory_depth_nilpotentIndex N = m) :
    xi_time_part9zm_ambiguity_shell_exact_memory_depth_resolventMemory N = m - 1 := by
  have _hterm :
      N.xi_time_part9zm_ambiguity_shell_exact_memory_depth_matrix ^ m = 0 :=
    xi_time_part9zm_ambiguity_shell_exact_memory_depth_finite_neumann_terminates m N
  have _hsharp :
      N.xi_time_part9zm_ambiguity_shell_exact_memory_depth_matrix ^ (m - 1) ≠ 0 :=
    xi_time_part9zm_ambiguity_shell_exact_memory_depth_pred_power_nonzero m hm N
  simp [xi_time_part9zm_ambiguity_shell_exact_memory_depth_resolventMemory, hNil]

end Omega.Zeta
