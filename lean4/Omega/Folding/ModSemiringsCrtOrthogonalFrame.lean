import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Omega.Core.Fib

namespace Omega

open scoped BigOperators

/-- A concrete two-slot orthogonal idempotent frame on `ZMod (F_{m+2})`. The first slot carries
the whole modulus and the second slot is the zero component. -/
def foldModCrtIdempotent (m : Nat) : Fin 2 → ZMod (Nat.fib (m + 2))
  | 0 => 1
  | 1 => 0

/-- The `i`-th component of `x` cut out by the chosen CRT idempotent. -/
def foldModCrtComponent (m : Nat) (x : ZMod (Nat.fib (m + 2))) (i : Fin 2) :
    ZMod (Nat.fib (m + 2)) :=
  foldModCrtIdempotent m i * x

/-- Concrete orthogonal-frame package for the fold-mod semiring over the Fibonacci modulus.
It records idempotence, pairwise orthogonality, the sum-to-one identity, and the canonical
component decomposition obtained by left multiplication with the frame. -/
def foldModSemiringsCrtOrthogonalFrame (m : Nat) : Prop :=
  (∀ i, foldModCrtIdempotent m i * foldModCrtIdempotent m i = foldModCrtIdempotent m i) ∧
    (∀ i j, i ≠ j → foldModCrtIdempotent m i * foldModCrtIdempotent m j = 0) ∧
    (∑ i : Fin 2, foldModCrtIdempotent m i = 1) ∧
    (∀ x : ZMod (Nat.fib (m + 2)), x = ∑ i : Fin 2, foldModCrtComponent m x i) ∧
    ∀ x : ZMod (Nat.fib (m + 2)), ∀ c : Fin 2 → ZMod (Nat.fib (m + 2)),
      (∀ i, c i = foldModCrtComponent m x i) → x = ∑ i : Fin 2, c i

/-- The canonical frame `[(1 : ZMod (F_{m+2})), 0]` is an orthogonal idempotent partition of
unity, and left multiplication by its entries gives the corresponding component decomposition.
    cor:fold-mod-semirings-crt-orthogonal-frame -/
theorem paper_fold_mod_semirings_crt_orthogonal_frame (m : Nat) :
    foldModSemiringsCrtOrthogonalFrame m := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [foldModCrtIdempotent]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [foldModCrtIdempotent]
  · rw [Fin.sum_univ_two]
    simp [foldModCrtIdempotent]
  · intro x
    rw [Fin.sum_univ_two]
    simp [foldModCrtComponent, foldModCrtIdempotent]
  · intro x c hc
    rw [Fin.sum_univ_two]
    rw [hc 0, hc 1]
    simp [foldModCrtComponent, foldModCrtIdempotent]

end Omega
