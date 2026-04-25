import Mathlib.Tactic
import Omega.Folding.FoldFourierPhaseLockingByComplement
import Omega.Folding.FiberWeightCountComplement

namespace Omega

open Omega.Folding

theorem paper_killo_fold_fourier_reflection_phase_rigidity (m : ℕ) :
    (∀ r : Fin (Nat.fib (m + 2)),
      weightCongruenceCount m r.1 =
        weightCongruenceCount m
          ((Nat.fib (m + 1) - 2 + Nat.fib (m + 2) - r.1) % Nat.fib (m + 2))) ∧
      FoldFourierPhaseLockingByComplement m := by
  refine ⟨?_, Omega.Folding.paper_fold_fourier_phase_locking_by_complement m⟩
  rcases m with _ | _ | m
  · intro r
    fin_cases r
    native_decide
  · intro r
    fin_cases r <;> native_decide
  · intro r
    have hm : 2 ≤ m + 2 := by omega
    have hfib_ge_two : 2 ≤ Nat.fib (m + 3) := by
      calc
        Nat.fib (m + 3) ≥ Nat.fib 3 := Nat.fib_mono (by omega)
        _ = 2 := by native_decide
    have hshift_lt : Nat.fib (m + 3) - 2 < Nat.fib (m + 4) := by
      have hmono : Nat.fib (m + 3) ≤ Nat.fib (m + 4) := Nat.fib_mono (by omega)
      omega
    have hstable :
        stableValue (complementAction (m := m + 2) (X.ofNat (m + 2) r.1)) =
          ((Nat.fib (m + 3) - 2 + Nat.fib (m + 4) - r.1) % Nat.fib (m + 4)) := by
      rw [complementAction, X.stableValue_stableSub, X.stableValue_ofNat_lt _ hshift_lt,
        X.stableValue_ofNat_lt _ r.2]
      rw [Nat.add_sub_assoc (Nat.le_of_lt r.2)]
    calc
      weightCongruenceCount (m + 2) r.1 = X.fiberMultiplicity (X.ofNat (m + 2) r.1) := by
        symm
        rw [fiberMultiplicity_eq_wcc, X.stableValue_ofNat_lt _ r.2]
      _ = X.fiberMultiplicity (complementAction (m := m + 2) (X.ofNat (m + 2) r.1)) := by
        symm
        exact fiberMultiplicity_complementAction (x := X.ofNat (m + 2) r.1) hm
      _ = weightCongruenceCount (m + 2)
            (stableValue (complementAction (m := m + 2) (X.ofNat (m + 2) r.1))) := by
              rw [fiberMultiplicity_eq_wcc]
      _ = weightCongruenceCount (m + 2)
            ((Nat.fib (m + 3) - 2 + Nat.fib (m + 4) - r.1) % Nat.fib (m + 4)) := by
              simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using congrArg
                (weightCongruenceCount (m + 2)) hstable

end Omega
