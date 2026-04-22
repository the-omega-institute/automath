import Mathlib
import Omega.POM.FractranFirstfitSerialDepth

namespace Omega.POM

/-- Total hard serial depth of `t` successive first-fit FRACTRAN calls with rule budget `k`. -/
def totalSerialDepth : Nat → Nat → Nat
  | 0, _ => 0
  | t + 1, k => totalSerialDepth t k + fractranSerialDepth k

/-- Paper label: `cor:pom-fractran-firstfit-total-serial-depth`. -/
theorem paper_pom_fractran_firstfit_total_serial_depth (t k : Nat) (hk : 1 ≤ k) :
    t * k ≤ totalSerialDepth t k := by
  induction t with
  | zero =>
      simp [totalSerialDepth]
  | succ t ih =>
      have hstep : k ≤ fractranSerialDepth k := (paper_pom_fractran_firstfit_serial_depth k hk).2
      calc
        (t + 1) * k = t * k + k := by rw [Nat.succ_mul]
        _ ≤ totalSerialDepth t k + fractranSerialDepth k := by omega
        _ = totalSerialDepth (t + 1) k := by simp [totalSerialDepth]

end Omega.POM
