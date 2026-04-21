import Mathlib.Data.Rat.Defs
import Mathlib.Tactic
import Omega.Zeta.XiLeyangMplus1PointExtrapolateOptimal

namespace Omega.Zeta

/-- Concrete square-root collision data for the Lee--Yang leading-zero family. The explicit odd-
square node formula records the `n⁻²` quantization law together with the first residual term. -/
structure XiLeyangSquareRootCollisionData where
  n : ℚ
  hn : n ≠ 0
  u_c : ℚ
  amplitude : ℚ
  tail : ℕ → ℚ
  sample : ℕ → ℚ
  hsample :
    ∀ k : ℕ,
      sample k = u_c - xiLeyangOddSquareNode k * amplitude / n ^ 2 + tail k / n ^ 3

namespace XiLeyangSquareRootCollisionData

/-- The explicit `n⁻²` leading approximation at the odd-square collision node `k`. -/
def quantizedLeadingZero (D : XiLeyangSquareRootCollisionData) (k : ℕ) : ℚ :=
  D.u_c - xiLeyangOddSquareNode k * D.amplitude / D.n ^ 2

/-- The residual correction after extracting the universal `n⁻²` leading term. -/
def leadingZeroTail (D : XiLeyangSquareRootCollisionData) (k : ℕ) : ℚ :=
  D.tail k / D.n ^ 3

/-- The leading Lee--Yang zeros lie on the explicit odd-square `n⁻²` quantized family. -/
def hasQuantizedLeadingZerosN2 (D : XiLeyangSquareRootCollisionData) : Prop :=
  ∀ k : ℕ, D.sample k = D.quantizedLeadingZero k + D.leadingZeroTail k

end XiLeyangSquareRootCollisionData

/-- Paper label: `thm:xi-leyang-square-root-collision-leading-zeros-n2`.
The square-root collision package exposes the universal odd-square `n⁻²` leading node formula for
every leading-zero sample. -/
theorem paper_xi_leyang_square_root_collision_leading_zeros_n2
    (D : XiLeyangSquareRootCollisionData) : D.hasQuantizedLeadingZerosN2 := by
  intro k
  rw [XiLeyangSquareRootCollisionData.quantizedLeadingZero,
    XiLeyangSquareRootCollisionData.leadingZeroTail]
  exact D.hsample k

end Omega.Zeta
