import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

namespace Omega.Zeta

open Matrix

/-- Paper label: `thm:xi-time-part9zm-ambiguity-shell-exact-nilpotent-index`.
The vanishing at `m` and nonvanishing at `m - 1` give the exact nilpotent index. -/
theorem paper_xi_time_part9zm_ambiguity_shell_exact_nilpotent_index (m : Nat)
    (N : Matrix (Fin m) (Fin m) Rat) (hm : 3 ≤ m) (hpow : N ^ m = 0)
    (hsharp : N ^ (m - 1) ≠ 0) :
    N ^ m = 0 ∧ N ^ (m - 1) ≠ 0 ∧ ∀ r : Nat, 1 ≤ r → N ^ r = 0 → m ≤ r := by
  refine ⟨hpow, hsharp, ?_⟩
  intro r hr hzr
  by_contra hmr
  have hrle : r ≤ m - 1 := by omega
  have hvanish : N ^ (m - 1) = 0 := by
    calc
      N ^ (m - 1) = N ^ (r + (m - 1 - r)) := by rw [Nat.add_sub_of_le hrle]
      _ = N ^ r * N ^ (m - 1 - r) := by rw [pow_add]
      _ = 0 := by simp [hzr]
  exact hsharp hvanish

end Omega.Zeta
