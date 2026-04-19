import Mathlib.Tactic
import Omega.GU.TerminalFoldbin6Histogram64To21

namespace Omega.GU

/-- A linear quotient model of the window-`6` terminal fold would force every nonempty fiber to
have the same coset cardinality `2^(6-k)`. -/
structure TerminalFoldbin6CosetModel (k : ℕ) : Prop where
  uniformFiberCardinality :
    ∃ c : ℕ, c = 2 ^ (6 - k) ∧ ∀ d : ℕ, cBinFiberHist 6 d ≠ 0 → c = d

/-- The certified window-`6` histogram has fibers of sizes `2`, `3`, and `4`, so it cannot come
from a linear-kernel coset partition with uniform power-of-two fiber size.
    cor:terminal-foldbin6-no-linear-kernel -/
theorem paper_terminal_foldbin6_no_linear_kernel : ¬ ∃ k, TerminalFoldbin6CosetModel k := by
  rintro ⟨k, M⟩
  rcases M.uniformFiberCardinality with ⟨c, _hcPow, hcUni⟩
  have h2hist : cBinFiberHist 6 2 ≠ 0 := by simp [cBinFiberHist_6_2]
  have h3hist : cBinFiberHist 6 3 ≠ 0 := by simp [cBinFiberHist_6_3]
  have h4hist : cBinFiberHist 6 4 ≠ 0 := by simp [cBinFiberHist_6_4]
  have h2 : c = 2 := hcUni 2 h2hist
  have h3 : c = 3 := hcUni 3 h3hist
  have h4 : c = 4 := hcUni 4 h4hist
  have h23 : (2 : ℕ) = 3 := h2.symm.trans h3
  have h34 : (3 : ℕ) = 4 := h3.symm.trans h4
  omega

end Omega.GU
