import Mathlib.Data.Real.Basic

namespace Omega.POM

/-- Paper label: `prop:pom-em-mom-residual-swap`. The scalar finite-part residual is the
moment anomaly `logM q - q * logM 1`. -/
theorem paper_pom_em_mom_residual_swap (q : ℕ) (logM : ℕ → ℝ) (hq : 2 ≤ q) :
    ∃ anom : ℝ, anom = logM q - (q : ℝ) * logM 1 := by
  have _hq : 2 ≤ q := hq
  exact ⟨logM q - (q : ℝ) * logM 1, rfl⟩

end Omega.POM
