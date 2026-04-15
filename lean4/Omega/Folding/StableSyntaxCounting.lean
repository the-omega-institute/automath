import Omega.Folding.StableSyntax

namespace Omega.Folding

set_option maxHeartbeats 400000 in
/-- Resolution-folding publication wrapper for Fibonacci counting of admissible words.
    cor:stable-syntax-counting -/
theorem paper_resolution_folding_stable_syntax_counting (m : ℕ) :
    Fintype.card (Omega.X m) = Nat.fib (m + 2) :=
  Omega.X.card_eq_fib m

end Omega.Folding
