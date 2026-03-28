import Omega.Folding.FiberWeightCount
import Omega.Folding.MomentRecurrence

namespace Omega

/-- Complement symmetry of weight congruence count:
    wcc(m, F_{m+1}-2-r) = wcc(m, r) for m ≥ 2.
    The bitwise complement maps weight w to F_{m+3}-2-weight(w),
    which shifts weight mod F_{m+2} by the complement constant F_{m+1}-2.
    prop:fold-fiber-count-reciprocity -/
theorem weightCongruenceCount_complement (m : Nat) (hm : 2 ≤ m) (r : Nat)
    (hr : r < Nat.fib (m + 2)) (hr2 : r ≤ Nat.fib (m + 1) - 2) :
    weightCongruenceCount m (Nat.fib (m + 1) - 2 - r) = weightCongruenceCount m r := by
  have hFpos : 0 < Nat.fib (m + 2) := fib_succ_pos (m + 1)
  have hF1le : Nat.fib (m + 1) ≤ Nat.fib (m + 2) := Nat.fib_mono (by omega)
  have hF3 : Nat.fib (m + 3) = Nat.fib (m + 1) + Nat.fib (m + 2) := Nat.fib_add_two
  have hF1_ge2 : 2 ≤ Nat.fib (m + 1) := by
    calc Nat.fib (m + 1) ≥ Nat.fib 3 := Nat.fib_mono (by omega)
      _ = 2 := by native_decide
  have hF1_2_lt : Nat.fib (m + 1) - 2 - r < Nat.fib (m + 2) := by omega
  rw [weightCongruenceCount_eq_sum_ewc m (Nat.fib (m + 1) - 2 - r) hF1_2_lt,
    weightCongruenceCount_eq_sum_ewc m r hr]
  -- Goal: ewc(m, F_{m+1}-2-r) + ewc(m, F_{m+1}-2-r+F_{m+2}) = ewc(m, r) + ewc(m, r+F_{m+2})
  -- Step 1: ewc(m, F_{m+1}-2-r) = ewc(m, r+F_{m+2}) via ewc symmetry
  -- F_{m+3}-2-(F_{m+1}-2-r) = F_{m+1}+F_{m+2}-2-F_{m+1}+2+r = F_{m+2}+r
  have hle1 : Nat.fib (m + 1) - 2 - r ≤ Nat.fib (m + 3) - 2 := by omega
  have h1 : exactWeightCount m (Nat.fib (m + 1) - 2 - r) =
      exactWeightCount m (r + Nat.fib (m + 2)) := by
    rw [exactWeightCount_symmetric m (Nat.fib (m + 1) - 2 - r) hle1]
    congr 1; omega
  -- Step 2: ewc(m, F_{m+1}-2-r+F_{m+2}) = ewc(m, r) via ewc symmetry
  -- F_{m+3}-2-(F_{m+1}-2-r+F_{m+2}) = F_{m+1}+F_{m+2}-2-F_{m+1}+2+r-F_{m+2} = r
  have hle2 : Nat.fib (m + 1) - 2 - r + Nat.fib (m + 2) ≤ Nat.fib (m + 3) - 2 := by omega
  have h2 : exactWeightCount m (Nat.fib (m + 1) - 2 - r + Nat.fib (m + 2)) =
      exactWeightCount m r := by
    rw [exactWeightCount_symmetric m _ hle2]
    congr 1; omega
  rw [h1, h2]; ring

end Omega
