import Mathlib.Tactic
import Omega.POM.FoldInversionZeroRateStrongConverse

namespace Omega.Folding

/-- Paper-facing wrapper around the fold Fano arithmetic: once the expected logarithmic fiber size
is dominated by the address conditional entropy, the register subtraction and Fano upper bound
force the side-information budget lower bound. -/
theorem paper_killo_fold_approx_address_fano_lower_bound (m sideInfoBits : ℕ)
    (delta expectedFiberLogCard hAX hR hAXR : ℝ) (hLower : expectedFiberLogCard ≤ hAX)
    (hSubtract : hAX - hR ≤ hAXR) (hRegister : hR ≤ sideInfoBits)
    (hFano : hAXR ≤ Omega.POM.pomFoldFanoUpperBound m delta) :
    expectedFiberLogCard - Omega.POM.pomBinaryEntropy delta - delta * m ≤ sideInfoBits := by
  have hFano' : hAXR ≤ Omega.POM.pomBinaryEntropy delta + delta * m := by
    simpa [Omega.POM.pomFoldFanoUpperBound] using hFano
  linarith

end Omega.Folding
