import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

namespace Omega.Conclusion

open Matrix

/-- Paper label: `thm:conclusion-ambiguity-shell-nilpotent-index-equals-window`. If a smaller
power vanished, multiplying by the remaining factor would force `N^(m - 1) = 0`, contradicting the
sharpness hypothesis. -/
theorem paper_conclusion_ambiguity_shell_nilpotent_index_equals_window (m : Nat)
    (N : Matrix (Fin m) (Fin m) Rat) (hm : 1 ≤ m) (hpow : N ^ m = 0) (hsharp : N ^ (m - 1) ≠ 0) :
    ∀ r : Nat, 1 ≤ r → N ^ r = 0 → m ≤ r := by
  let _ := hpow
  intro r hr hzr
  by_contra hmr
  have hrlt : r < m := lt_of_not_ge hmr
  have hrle : r ≤ m - 1 := by
    omega
  have hvanish : N ^ (m - 1) = 0 := by
    calc
      N ^ (m - 1) = N ^ (r + (m - 1 - r)) := by rw [Nat.add_sub_of_le hrle]
      _ = N ^ r * N ^ (m - 1 - r) := by rw [pow_add]
      _ = 0 := by simp [hzr]
  exact hsharp hvanish

end Omega.Conclusion
