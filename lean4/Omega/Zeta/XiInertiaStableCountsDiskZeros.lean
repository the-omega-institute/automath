import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete audit data for reading disk-zero counts from stabilized Toeplitz inertia. -/
structure xi_inertia_stable_counts_disk_zeros_data where
  diskZeroCount : ℕ
  diskPoleCount : ℕ
  negativeSquareIndex : ℕ
  stableToeplitzInertia : ℕ
  rhDiskZeroCount : ℕ
  diskZeroPoleCorrespondence : diskZeroCount = diskPoleCount
  negativeSquareEquivalence : diskPoleCount = negativeSquareIndex
  toeplitzInertiaStabilization : stableToeplitzInertia = negativeSquareIndex
  rhZeroDiskCorrespondence : rhDiskZeroCount = diskZeroCount

/-- The stabilized finite Toeplitz inertia recovers the disk-zero count and hence the
corresponding RH-zero count recorded by the same disk interface. -/
def xi_inertia_stable_counts_disk_zeros_data.statement
    (D : xi_inertia_stable_counts_disk_zeros_data) : Prop :=
  D.stableToeplitzInertia = D.diskZeroCount ∧
    D.rhDiskZeroCount = D.stableToeplitzInertia

/-- Paper label: `cor:xi-inertia-stable-counts-disk-zeros`. -/
theorem paper_xi_inertia_stable_counts_disk_zeros
    (D : xi_inertia_stable_counts_disk_zeros_data) : D.statement := by
  have hstable : D.stableToeplitzInertia = D.diskZeroCount := by
    rw [D.toeplitzInertiaStabilization, ← D.negativeSquareEquivalence,
      ← D.diskZeroPoleCorrespondence]
  constructor
  · exact hstable
  · rw [D.rhZeroDiskCorrespondence, hstable]

end Omega.Zeta
