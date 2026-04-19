import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Fibonacci
import Mathlib.Tactic

namespace Omega.POM

/-- Base-2 logarithm used throughout the fold-inversion bitrate statements. -/
noncomputable def log2 (x : ℝ) : ℝ :=
  Real.log x / Real.log 2

/-- The binary entropy function written in base `2`. -/
noncomputable def pomBinaryEntropy (ε : ℝ) : ℝ :=
  -(ε * log2 ε + (1 - ε) * log2 (1 - ε))

/-- The fold-side information gap `m - log₂ F_{m+2}` from the paper statement. -/
noncomputable def pomFoldInformationGapBits (m : ℕ) : ℝ :=
  (m : ℝ) - log2 (Nat.fib (m + 2))

/-- The Fano upper bound `h₂(ε) + ε m` appearing in the strong converse estimate. -/
noncomputable def pomFoldFanoUpperBound (m : ℕ) (ε : ℝ) : ℝ :=
  pomBinaryEntropy ε + ε * m

/-- Paper-facing strong-converse arithmetic wrapper: once the conditional-entropy lower bound
`H(U | X) ≥ m - log₂ F_{m+2}`, the register subtraction `H(R) ≤ B`, the residual entropy bound
`H(U | X, R) ≥ H(U | X) - H(R)`, and the Fano estimate
`H(U | X, R) ≤ h₂(ε) + ε m` are available, the advertised lower bound on the side-information
budget follows immediately.
    thm:pom-fold-inversion-zero-rate-strong-converse -/
theorem paper_pom_fold_inversion_zero_rate_strong_converse
    (m B : ℕ) (ε hUX hR hUXR : ℝ)
    (hLower : pomFoldInformationGapBits m ≤ hUX)
    (hSubtract : hUX - hR ≤ hUXR)
    (hRegister : hR ≤ (B : ℝ))
    (hFano : hUXR ≤ pomFoldFanoUpperBound m ε) :
    pomFoldInformationGapBits m - pomBinaryEntropy ε - ε * m ≤ (B : ℝ) := by
  have hFano' : hUXR ≤ pomBinaryEntropy ε + ε * m := by
    simpa [pomFoldFanoUpperBound] using hFano
  linarith

end Omega.POM
