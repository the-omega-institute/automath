import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- Coefficient extraction along the `k`-th arithmetic progression. -/
def abel_decimation_semigroup_identity_decimate (a : ℕ → ℂ) (k : ℕ) : ℕ → ℂ :=
  fun n => a (k * n)

/-- Paper label: `prop:abel-decimation-semigroup-identity`. Composing two decimations multiplies
their step sizes. -/
theorem paper_abel_decimation_semigroup_identity (a : ℕ → ℂ) (k l : ℕ) :
    (fun n => a (k * (l * n))) = fun n => a ((k * l) * n) := by
  funext n
  simp [Nat.mul_assoc]

end

end Omega.Zeta
