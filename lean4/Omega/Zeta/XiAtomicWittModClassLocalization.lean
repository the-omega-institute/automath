import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

/-- Paper label: `thm:xi-atomic-witt-mod-class-localization`. A single coefficient
perturbation at `n = 2` localizes to the matching residue class in every finite truncation. -/
theorem paper_xi_atomic_witt_mod_class_localization {R : Type*} [Semiring R]
    (m N : Nat) (hm : 2 ≤ m) (a : ZMod m) (u z : R) (p pcore : Nat → R)
    (hcoeff : ∀ n, p n = pcore n + if n = 2 then u else 0) :
    (Finset.range N).sum (fun n => if (n : ZMod m) = a then p n * z ^ n else 0) =
      (if (2 : ZMod m) = a then if 2 < N then u * z ^ 2 else 0 else 0) +
        (Finset.range N).sum
          (fun n => if (n : ZMod m) = a then pcore n * z ^ n else 0) := by
  classical
  let _ := hm
  have hsplit :
      (Finset.range N).sum (fun n => if (n : ZMod m) = a then p n * z ^ n else 0) =
        (Finset.range N).sum
            (fun n => if (n : ZMod m) = a then pcore n * z ^ n else 0) +
          (Finset.range N).sum
            (fun n => if (n : ZMod m) = a then (if n = 2 then u else 0) * z ^ n else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [hcoeff n]
    by_cases hclass : (n : ZMod m) = a
    · simp [hclass, add_mul]
    · simp [hclass]
  have hatom :
      (Finset.range N).sum
          (fun n => if (n : ZMod m) = a then (if n = 2 then u else 0) * z ^ n else 0) =
        if (2 : ZMod m) = a then if 2 < N then u * z ^ 2 else 0 else 0 := by
    by_cases hN : 2 < N
    · have hmem : 2 ∈ Finset.range N := by simpa using hN
      rw [Finset.sum_eq_single 2]
      · simp [hN]
      · intro n hn hne
        simp [hne]
      · intro hnot
        exact (hnot hmem).elim
    · have hnotmem : 2 ∉ Finset.range N := by simpa using hN
      rw [Finset.sum_eq_zero]
      · simp [hN]
      · intro n hn
        have hne : n ≠ 2 := by
          intro h
          exact hnotmem (by simpa [h] using hn)
        simp [hne]
  rw [hsplit, hatom]
  rw [add_comm]

end Omega.Zeta
