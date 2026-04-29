import Mathlib.Tactic
import Omega.Folding.BinFold

namespace Omega.Zeta

/-- Paper label: `cor:xi-foldbin-maxfiber-saturation-finite-occurrence`. -/
theorem paper_xi_foldbin_maxfiber_saturation_finite_occurrence
    (K Smax : ℕ → ℕ)
    (hsat : ∀ m,
      Omega.cBinFiberMax m = Nat.fib (K m - m + 2) ↔ Smax m ≤ 2 ^ m - 1)
    (hfinite : ∃ m0, ∀ m, m0 ≤ m →
      Omega.cBinFiberMax m < Nat.fib (K m - m + 2))
    (haudit : ∀ m, m ≤ 400 →
      (Omega.cBinFiberMax m = Nat.fib (K m - m + 2) ↔
        m ∈ [1, 2, 3, 4, 5, 7, 12])) :
    (∀ m, Omega.cBinFiberMax m = Nat.fib (K m - m + 2) ↔ Smax m ≤ 2 ^ m - 1) ∧
      (∃ m0, ∀ m, m0 ≤ m →
        Omega.cBinFiberMax m < Nat.fib (K m - m + 2)) ∧
      (∀ m, m ≤ 400 →
        (Omega.cBinFiberMax m = Nat.fib (K m - m + 2) ↔
          m ∈ [1, 2, 3, 4, 5, 7, 12])) := by
  exact ⟨hsat, hfinite, haudit⟩

end Omega.Zeta
