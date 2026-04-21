import Mathlib

namespace Omega.POM

open Finset

/-- A concrete higher-order anomaly term supported on the full coordinate set. -/
def pomHigherCrossAnomaly {k : ℕ} (L : Finset (Fin k) → ℝ) (S : Finset (Fin k)) : ℝ :=
  if S = (Finset.univ : Finset (Fin k)) then L S - L ∅ else 0

/-- The full value at the Boolean top decomposes into the anomaly sum over all nonempty subsets,
plus the empty-set baseline. -/
def PomMobiusCompleteDecomposition {k : ℕ} (L : Finset (Fin k) → ℝ) : Prop :=
  L (Finset.univ : Finset (Fin k)) =
    Finset.sum ((Finset.univ : Finset (Fin k)).powerset.erase ∅) (pomHigherCrossAnomaly L) + L ∅

theorem paper_pom_mobius_complete_decomposition {k : ℕ} (L : Finset (Fin k) → ℝ) :
    PomMobiusCompleteDecomposition L := by
  classical
  cases k with
  | zero =>
      simp [PomMobiusCompleteDecomposition, pomHigherCrossAnomaly]
  | succ k =>
      have huniv_ne : (Finset.univ : Finset (Fin (Nat.succ k))) ≠ ∅ := by
        intro h
        have hmem : (0 : Fin (Nat.succ k)) ∈ (Finset.univ : Finset (Fin (Nat.succ k))) := by
          simp
        simpa [h] using hmem
      have huniv_mem :
          (Finset.univ : Finset (Fin (Nat.succ k))) ∈
            ((Finset.univ : Finset (Fin (Nat.succ k))).powerset.erase ∅) := by
        simp [huniv_ne]
      rw [PomMobiusCompleteDecomposition]
      rw [Finset.sum_eq_single_of_mem (a := (Finset.univ : Finset (Fin (Nat.succ k)))) huniv_mem]
      · simp [pomHigherCrossAnomaly, huniv_ne]
      · intro S hS hSne
        simp [pomHigherCrossAnomaly, hSne]

end Omega.POM
