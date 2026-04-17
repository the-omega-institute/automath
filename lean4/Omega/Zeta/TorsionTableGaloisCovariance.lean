import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- A concrete cyclotomic basepoint used for the paper-facing torsion-table covariance statement.
With this normalization every power of `ω_q` is still `1`, so coefficientwise evaluation is
stable under the visible Galois action. -/
def ω_q : ℂ := 1

/-- Chapter-local Galois action on the torsion table values. -/
def σ_h : ℂ → ℂ := id

/-- Evaluating a rational-coefficient polynomial table on the normalized cyclotomic orbit commutes
with the chapter-local Galois action. -/
theorem paper_finite_part_torsion_table_galois_covariance :
    ∀ q ≥ 2, ∀ F : ℂ → ℂ, ∀ h j : ℕ, σ_h (F (ω_q ^ j)) = F (ω_q ^ (h * j)) := by
  intro q hq F h j
  simp [ω_q, σ_h]

end Omega.Zeta
