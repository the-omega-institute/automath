import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic
import Omega.Zeta.XiMittagLefflerUniversalKfoldJordanCollision

namespace Omega.Zeta

open Filter
open Omega.POM

/-- Paper label: `cor:xi-mittag-leffler-kfold-zero-quantization`.
Specializing the universal `k`-fold Jordan collision package to the simple-zero slot `r = 1`
identifies the limiting coefficient explicitly. In that slot the limiting coefficient vanishes
exactly when the collision parameter vanishes, which is the project's concrete simple-zero
persistence corollary. -/
theorem paper_xi_mittag_leffler_kfold_zero_quantization
    (k n : ℕ) (u C ρ : ℝ) (hρ : |ρ| ≤ 1) :
    xiJordanUniversalKernelCoeff k 1 u =
      (-u) / (Nat.factorial (pomKCollisionMittagLefflerOrder k 1) : ℝ) ∧
      (xiJordanUniversalKernelCoeff k 1 u = 0 ↔ u = 0) ∧
      Tendsto (fun _ : ℕ => xiJordanUniversalKernelCoeff k 1 u) atTop
        (nhds (xiJordanUniversalKernelCoeff k 1 u)) ∧
      |xiJordanFullFamily k 1 n u C ρ - xiJordanDominantBlockCoeff k 1 n u| ≤ |C| := by
  rcases paper_xi_mittag_leffler_universal_kfold_jordan_collision k 1 n u C ρ hρ with
    ⟨_, hml, _, _, hbound⟩
  have hml' :
      xiJordanUniversalKernelCoeff k 1 u =
        (-u) / (Nat.factorial (pomKCollisionMittagLefflerOrder k 1) : ℝ) := by
    simpa using hml
  have hiff : xiJordanUniversalKernelCoeff k 1 u = 0 ↔ u = 0 := by
    rw [hml']
    constructor
    · intro hzero
      have hfac_ne : (Nat.factorial (pomKCollisionMittagLefflerOrder k 1) : ℝ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero (pomKCollisionMittagLefflerOrder k 1)
      rcases (div_eq_zero_iff.mp hzero) with hnum | hden
      · exact neg_eq_zero.mp hnum
      · exact (hfac_ne hden).elim
    · intro hu
      simp [hu]
  exact ⟨hml', hiff, tendsto_const_nhds, hbound⟩

end Omega.Zeta
