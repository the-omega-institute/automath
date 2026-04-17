import Mathlib.Data.Nat.Fib.Zeckendorf
import Mathlib.Tactic
import Omega.Folding.BinFold
import Omega.Folding.MaxFiber
import Omega.Folding.OstrowskiDenominators

namespace Omega.GU

open Omega.Folding.OstrowskiDenominators

/-- On the golden branch, the Ostrowski denominators are Fibonacci numbers, the legal digit
language is exactly the Zeckendorf no-adjacent-ones syntax, and `cBinFold` is the corresponding
length-`m` prefix truncation of `Nat.zeckendorf`.
    cor:terminal-ostrowski-zeckendorf-binfold -/
theorem paper_terminal_ostrowski_zeckendorf_binfold (m N : Nat) :
    ostrowskiDenom (fun _ => 1) m = Nat.fib (m + 1) ∧
      (Nat.zeckendorf N).IsZeckendorfRep ∧
      (∀ i : Fin m, (Omega.cBinFold m N).1 i = true ↔ i.1 + 2 ∈ Nat.zeckendorf N) ∧
      Omega.X.restrict (Omega.cBinFold (m + 1) N) = Omega.cBinFold m N := by
  refine ⟨ostrowskiDenom_const_one_eq_fib m, Nat.isZeckendorfRep_zeckendorf N, ?_, ?_⟩
  · intro i
    simpa [Omega.cBinFold, Omega.get, i.isLt] using
      (Omega.X.get_ofNat_eq_true_iff (m := m) (n := N) (i := i.1) i.isLt)
  · simpa [Omega.cBinFold] using (Omega.restrict_ofNat m N)

end Omega.GU
