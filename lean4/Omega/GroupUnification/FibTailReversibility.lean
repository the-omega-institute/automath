import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic
import Omega.Core.Fib

namespace Omega.GroupUnification

/-- Even-index Fibonacci tail matrices are `SL₂(ℤ)` and conjugate to their inverse by
    `diag(-1,1)`.
    prop:fib-tail-reversibility -/
theorem paper_fib_tail_reversibility (m : Nat) (hm : Even m) :
    let G : Matrix (Fin 2) (Fin 2) ℤ :=
      !![(Nat.fib (m + 3) : ℤ), (Nat.fib (m + 2) : ℤ);
         (Nat.fib (m + 4) : ℤ), (Nat.fib (m + 3) : ℤ)]
    let R : Matrix (Fin 2) (Fin 2) ℤ := !![(-1 : ℤ), 0; 0, 1]
    G.det = 1 ∧
      R * G * R =
        !![(Nat.fib (m + 3) : ℤ), -((Nat.fib (m + 2) : ℤ));
           -((Nat.fib (m + 4) : ℤ)), (Nat.fib (m + 3) : ℤ)] := by
  dsimp
  refine ⟨?_, ?_⟩
  · rw [Matrix.det_fin_two]
    simp
    have hm2 : Even (m + 2) := hm.add (by decide : Even 2)
    have hCassNat :
        Nat.fib (m + 2) * Nat.fib (m + 4) + 1 = Nat.fib (m + 3) ^ 2 :=
      Omega.fib_cassini_even (m + 2) hm2
    have hCass :
        (Nat.fib (m + 2) : ℤ) * Nat.fib (m + 4) + 1 = (Nat.fib (m + 3) : ℤ) ^ 2 := by
      exact_mod_cast hCassNat
    rw [pow_two] at hCass
    nlinarith
  · ext i j <;> fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]

end Omega.GroupUnification
