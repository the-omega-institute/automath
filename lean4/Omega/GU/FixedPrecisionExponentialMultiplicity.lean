import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic

namespace Omega.GU

open scoped BigOperators

set_option maxHeartbeats 400000 in
/-- Finite precision partitions the `2^k` microstates into `m` buckets, so some bucket contains at
least the average multiplicity.
    thm:group-jg-fixed-precision-exponential-multiplicity -/
theorem paper_gut_fixed_precision_exponential_multiplicity
    (k m : ℕ) (bucket : Finset (Fin k) → Fin m) (hm : 0 < m) :
    ∃ y : Fin m, m * Fintype.card {s : Finset (Fin k) // bucket s = y} ≥ 2 ^ k := by
  classical
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  let fiberSize : Fin m → ℕ := fun y => Fintype.card {s : Finset (Fin k) // bucket s = y}
  obtain ⟨y, hyMem, hyMax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Fin m)) fiberSize Finset.univ_nonempty
  refine ⟨y, ?_⟩
  have hsum : Finset.univ.sum fiberSize = 2 ^ k := by
    calc
      Finset.univ.sum fiberSize
          = (Finset.univ : Finset (Fin m)).sum
              (fun z => ((Finset.univ : Finset (Finset (Fin k))).filter
                fun s => bucket s = z).card) := by
                  simp [fiberSize, Fintype.card_subtype]
      _ = (Finset.univ : Finset (Finset (Fin k))).card := by
        symm
        exact Finset.card_eq_sum_card_fiberwise (f := bucket) (s := Finset.univ)
          (t := Finset.univ) (by intro s hs; simp)
      _ = 2 ^ k := by simp
  have hle :
      Finset.univ.sum fiberSize ≤ Finset.univ.sum (fun _z : Fin m => fiberSize y) := by
    exact Finset.sum_le_sum (fun z hz => hyMax z (by simp at hz; simpa using hz))
  have havg : 2 ^ k ≤ m * fiberSize y := by
    calc
      2 ^ k = Finset.univ.sum fiberSize := hsum.symm
      _ ≤ Finset.univ.sum (fun _z : Fin m => fiberSize y) := hle
      _ = m * fiberSize y := by simp [fiberSize]
  simpa [fiberSize, ge_iff_le] using havg

/-- Paper-facing wrapper for the group-JG label.
    thm:group-jg-fixed-precision-exponential-multiplicity -/
theorem paper_group_jg_fixed_precision_exponential_multiplicity
    (k m : Nat) (bucket : Finset (Fin k) → Fin m) (hm : 0 < m) :
    ∃ y : Fin m, m * Fintype.card {s : Finset (Fin k) // bucket s = y} ≥ 2 ^ k := by
  exact paper_gut_fixed_precision_exponential_multiplicity k m bucket hm

end Omega.GU
