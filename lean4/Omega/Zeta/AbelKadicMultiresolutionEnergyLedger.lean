import Mathlib.Tactic
import Omega.Zeta.AbelDetailEnergyBudget

namespace Omega.Zeta

open scoped BigOperators

/-- Total `k`-adic block energy at resolution level `M`. -/
def abel_kadic_multiresolution_energy_ledger_block_energy
    (a : ℕ → ℚ) (k M N : ℕ) : ℚ :=
  Finset.sum (Finset.range (k * N)) (fun n => (a (k ^ M * n)) ^ 2)

/-- Coarse energy after one more `k`-adic decimation step. -/
def abel_kadic_multiresolution_energy_ledger_coarse_energy
    (a : ℕ → ℚ) (k M N : ℕ) : ℚ :=
  Finset.sum (Finset.range N) (fun q => (a (k ^ M * q)) ^ 2)

/-- Exact residue-class slice inside the `M`-th `k`-adic layer. -/
def abel_kadic_multiresolution_energy_ledger_valuation_slice
    (a : ℕ → ℚ) (k M N j : ℕ) : ℚ :=
  Finset.sum (Finset.range N) (fun q => (a (k ^ M * (k * q + j))) ^ 2)

/-- The nontrivial `k`-adic detail energy at level `M`. -/
def abel_kadic_multiresolution_energy_ledger_detail_energy
    (a : ℕ → ℚ) (k M N : ℕ) : ℚ :=
  Finset.sum (Finset.range (k - 1))
    (fun j => abel_kadic_multiresolution_energy_ledger_valuation_slice a k M N (j + 1))

/-- Paper label: `cor:abel-kadic-multiresolution-energy-ledger`. Applying the one-step Hardy
energy split to the decimated sequence `n ↦ a (k^M n)` isolates the next coarse block and the
exact nontrivial residue slices in the `M`-th `k`-adic layer. -/
theorem paper_abel_kadic_multiresolution_energy_ledger
    (a : ℕ → ℚ) (k M N : ℕ) (hk : 0 < k) :
    let coarse := abel_kadic_multiresolution_energy_ledger_coarse_energy a k (M + 1) N
    let detail := abel_kadic_multiresolution_energy_ledger_detail_energy a k M N
    detail = abel_kadic_multiresolution_energy_ledger_block_energy a k M N - coarse ∧
      0 ≤ detail ∧
      ((∃ j, j < k ∧ 0 < j ∧
          0 < abel_kadic_multiresolution_energy_ledger_valuation_slice a k M N j) →
        0 < detail) := by
  simpa [abel_kadic_multiresolution_energy_ledger_block_energy,
    abel_kadic_multiresolution_energy_ledger_coarse_energy,
    abel_kadic_multiresolution_energy_ledger_detail_energy,
    abel_kadic_multiresolution_energy_ledger_valuation_slice,
    Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
    (paper_abel_detail_energy_budget (fun n => a (k ^ M * n)) k N hk)

end Omega.Zeta
