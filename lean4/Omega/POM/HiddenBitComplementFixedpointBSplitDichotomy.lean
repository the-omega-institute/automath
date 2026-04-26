import Mathlib.Tactic
import Omega.Folding.FiberWeightCount
import Omega.Folding.MomentRecurrence

namespace Omega.POM

/-- Paper label: `prop:pom-hiddenbit-complement-fixedpoint-bsplit-dichotomy`. After splitting on
the parity of `F_{m+1}`, one can choose a stable residue class whose lower and upper hidden-bit
branches are either paired by the exact-weight symmetry or forced to vanish above the maximal
weight. -/
theorem paper_pom_hiddenbit_complement_fixedpoint_bsplit_dichotomy (m : ℕ) :
    Odd (Nat.fib (m + 2)) → ∃ x : X m,
      ((Even (Nat.fib (m + 1)) → fiberHiddenBitCount 0 x = fiberHiddenBitCount 1 x) ∧
        (Odd (Nat.fib (m + 1)) → fiberHiddenBitCount 1 x = 0)) := by
  intro _hOdd
  by_cases hEven : Even (Nat.fib (m + 1))
  · rcases hEven with ⟨k, hk⟩
    refine ⟨X.ofNat m (k - 1), ?_⟩
    constructor
    · intro _hPrevEven
      have hk_pos : 1 ≤ k := by
        have hfib_pos : 0 < Nat.fib (m + 1) := Nat.fib_pos.mpr (by omega)
        omega
      have hk_lt : k - 1 < Nat.fib (m + 2) := by
        have hmono : Nat.fib (m + 1) ≤ Nat.fib (m + 2) := Nat.fib_mono (by omega)
        omega
      have hsv : stableValue (X.ofNat m (k - 1)) = k - 1 := X.stableValue_ofNat_lt _ hk_lt
      rw [fiberHiddenBitCount_zero_eq_ewc, fiberHiddenBitCount_one_eq_ewc, hsv]
      have hle : k - 1 + Nat.fib (m + 2) ≤ Nat.fib (m + 3) - 2 := by
        have hfib3 : Nat.fib (m + 3) = Nat.fib (m + 1) + Nat.fib (m + 2) := Nat.fib_add_two
        omega
      rw [exactWeightCount_symmetric m (k - 1 + Nat.fib (m + 2)) hle]
      have hcomp : Nat.fib (m + 3) - 2 - (k - 1 + Nat.fib (m + 2)) = k - 1 := by
        have hfib3 : Nat.fib (m + 3) = Nat.fib (m + 1) + Nat.fib (m + 2) := Nat.fib_add_two
        omega
      simp [hcomp]
    · intro hOddPrev
      exact (Nat.not_even_iff_odd.mpr hOddPrev ⟨k, hk⟩).elim
  · refine ⟨X.ofNat m (Nat.fib (m + 1) - 1), ?_⟩
    constructor
    · intro hPrevEven
      exact (hEven hPrevEven).elim
    · intro _
      have hr_lt : Nat.fib (m + 1) - 1 < Nat.fib (m + 2) := by
        have hprev_pos : 0 < Nat.fib (m + 1) := Nat.fib_pos.mpr (by omega)
        have hmono : Nat.fib (m + 1) ≤ Nat.fib (m + 2) := Nat.fib_mono (by omega)
        omega
      have hsv : stableValue (X.ofNat m (Nat.fib (m + 1) - 1)) = Nat.fib (m + 1) - 1 :=
        X.stableValue_ofNat_lt _ hr_lt
      rw [fiberHiddenBitCount_one_eq_ewc, hsv]
      unfold exactWeightCount
      apply Finset.card_eq_zero.mpr
      rw [Finset.filter_eq_empty_iff]
      intro w _ hw
      have hmax : weight w ≤ Nat.fib (m + 3) - 2 := weight_le_allTrue w
      have hfib3 : Nat.fib (m + 3) = Nat.fib (m + 1) + Nat.fib (m + 2) := Nat.fib_add_two
      omega

end Omega.POM
