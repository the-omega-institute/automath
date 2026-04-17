import Mathlib.Data.Int.Fib.Lemmas
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

namespace Omega.Folding

/-- A d'Ocagne-style Fibonacci compression identity used in the fold-resonance formulas. -/
theorem paper_fold_resonance_docagne
    (m j : Nat) (hm : 1 <= m) (hj : 1 <= j) (hjm : j <= m) :
    ((Nat.fib m : Int) * (Nat.fib (j + 1) : Int) -
        (Nat.fib (j - 1) : Int) * (Nat.fib (m + 2) : Int) =
      ((-1 : Int) ^ (j + 1)) * (Nat.fib (m + 1 - j) : Int)) := by
  let a : Nat := m + 1 - j
  have hmrec : Int.fib (m + 2 : Int) = Int.fib (m : Int) + Int.fib (m + 1 : Int) := by
    simpa using Int.fib_add_two (m : Int)
  have hjrecNat : Nat.fib (j + 1) = Nat.fib (j - 1) + Nat.fib j := by
    simpa using Nat.fib_add_one (Nat.ne_of_gt hj)
  have hjInt : (j : Int) - 1 = (j - 1 : Nat) := by
    omega
  have hsubInt : (m : Int) - j = (m - j : Nat) := by
    omega
  have hm1Int : (m : Int) + 1 = (m + 1 : Nat) := by
    omega
  have hm2Int : (m : Int) + 2 = (m + 2 : Nat) := by
    omega
  have hj1Int : (j : Int) + 1 = (j + 1 : Nat) := by
    omega
  have hj2Int : (j : Int) + 2 = (j + 2 : Nat) := by
    omega
  have hjrec : Int.fib (j + 1 : Int) = Int.fib (j - 1 : Int) + Int.fib (j : Int) := by
    simpa [hjInt, Int.fib_natCast] using congrArg (fun n : Nat => (n : Int)) hjrecNat
  have hA : Int.fib (m + 1 : Int) =
      Int.fib (m - j : Int) * Int.fib (j : Int) + Int.fib (a : Int) * Int.fib (j + 1 : Int) := by
    have hA_nat := Nat.fib_add (m - j) j
    have hsum1 : (m - j) + j + 1 = m + 1 := by omega
    have hsub1 : m - j + 1 = m + 1 - j := by omega
    rw [hsum1, hsub1] at hA_nat
    have hA_cast : (Nat.fib (m + 1) : Int) =
        (Nat.fib (m - j) : Int) * (Nat.fib j : Int) + (Nat.fib a : Int) * (Nat.fib (j + 1) : Int) :=
      congrArg (fun n : Nat => (n : Int)) hA_nat
    rw [hm1Int, hsubInt, hj1Int, Int.fib_natCast, Int.fib_natCast, Int.fib_natCast, Int.fib_natCast]
    exact hA_cast
  have hB : Int.fib (m + 2 : Int) =
      Int.fib (m - j : Int) * Int.fib (j + 1 : Int) + Int.fib (a : Int) * Int.fib (j + 2 : Int) := by
    have hB_nat := Nat.fib_add (m - j) (j + 1)
    have hsum2 : (m - j) + (j + 1) + 1 = m + 2 := by omega
    have hsub1 : m - j + 1 = m + 1 - j := by omega
    rw [hsum2, hsub1] at hB_nat
    have hB_cast : (Nat.fib (m + 2) : Int) =
        (Nat.fib (m - j) : Int) * (Nat.fib (j + 1) : Int) + (Nat.fib a : Int) * (Nat.fib (j + 2) : Int) :=
      congrArg (fun n : Nat => (n : Int)) hB_nat
    rw [hm2Int, hsubInt, hj1Int, hj2Int, Int.fib_natCast, Int.fib_natCast, Int.fib_natCast, Int.fib_natCast]
    exact hB_cast
  have hCassini :
      Int.fib (j : Int) * Int.fib (j + 2 : Int) - Int.fib (j + 1 : Int) ^ 2 =
        (-1 : Int) ^ (j + 1) := by
    simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using
      Int.fib_succ_mul_fib_pred_sub_fib_sq (j + 1 : Int)
  have hm0 : Int.fib (m : Int) = Int.fib (m + 2 : Int) - Int.fib (m + 1 : Int) := by
    linarith
  have hj0 : Int.fib (j - 1 : Int) = Int.fib (j + 1 : Int) - Int.fib (j : Int) := by
    linarith
  calc
    ((Nat.fib m : Int) * (Nat.fib (j + 1) : Int) -
        (Nat.fib (j - 1) : Int) * (Nat.fib (m + 2) : Int))
        = Int.fib (m : Int) * Int.fib (j + 1 : Int) -
            Int.fib (j - 1 : Int) * Int.fib (m + 2 : Int) := by
          rw [hj1Int, hm2Int, hjInt, Int.fib_natCast, Int.fib_natCast, Int.fib_natCast, Int.fib_natCast]
    _ = Int.fib (j : Int) * Int.fib (m + 2 : Int) -
          Int.fib (m + 1 : Int) * Int.fib (j + 1 : Int) := by
      rw [hm0, hj0]
      ring
    _ = ((-1 : Int) ^ (j + 1)) * Int.fib (a : Int) := by
      have hCassiniAlt :
          Int.fib (j : Int) * Int.fib (j + 2 : Int) - Int.fib (j + 1 : Int) ^ 2 =
            -((-1 : Int) ^ j) := by
        simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using hCassini
      have hCassiniMul :=
        congrArg (fun t : Int => Int.fib (a : Int) * t) hCassiniAlt
      rw [hA, hB]
      ring_nf
      ring_nf at hCassiniMul
      simpa [mul_comm, mul_left_comm, mul_assoc] using hCassiniMul
    _ = ((-1 : Int) ^ (j + 1)) * (Nat.fib (m + 1 - j) : Int) := by
      simp [a]

end Omega.Folding
