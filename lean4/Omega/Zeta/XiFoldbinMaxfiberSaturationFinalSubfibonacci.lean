import Mathlib.Tactic
import Omega.Folding.BinFold

namespace Omega.Zeta

/-- Paper label: `thm:xi-foldbin-maxfiber-saturation-final-subfibonacci`. -/
theorem paper_xi_foldbin_maxfiber_saturation_final_subfibonacci
    (K maxTail threshold : ℕ → ℕ)
    (hsat : ∀ m,
      Omega.cBinFiberMax m = Nat.fib (K m - m + 2) ↔ maxTail m ≤ threshold m)
    (hfinite : ∃ m0, ∀ m, m0 ≤ m →
      Omega.cBinFiberMax m < Nat.fib (K m - m + 2)) :
    (∀ m, Omega.cBinFiberMax m = Nat.fib (K m - m + 2) ↔
        maxTail m ≤ threshold m) ∧
      ∃ m0, ∀ m, m0 ≤ m →
        Omega.cBinFiberMax m ≤ Nat.fib (K m - m + 2) - 1 := by
  refine ⟨hsat, ?_⟩
  rcases hfinite with ⟨m0, hm0⟩
  refine ⟨m0, ?_⟩
  intro m hm
  exact Nat.le_sub_one_of_lt (hm0 m hm)

end Omega.Zeta
