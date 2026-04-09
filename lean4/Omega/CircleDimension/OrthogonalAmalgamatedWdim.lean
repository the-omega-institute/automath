import Mathlib.Tactic

namespace Omega.CircleDimension

/-- Weighted circle dimension `wdim u v = u + v / 2`.
    thm:cdim-orthogonal-amalgamated-wdim -/
def wdim (u v : ℚ) : ℚ := u + v / 2

/-- `wdim 0 0 = 0`.
    thm:cdim-orthogonal-amalgamated-wdim -/
theorem wdim_zero_zero : wdim 0 0 = 0 := by
  unfold wdim
  ring

/-- Closed form of `wdim`.
    thm:cdim-orthogonal-amalgamated-wdim -/
theorem wdim_u_linear (u v : ℚ) : wdim u v = u + v / 2 := rfl

/-- Amalgamated formula: identifying a shared subgroup of `wdim` `k` at the
    free-rank level subtracts `k`.
    thm:cdim-orthogonal-amalgamated-wdim -/
theorem wdim_amalgamated (u₁ v₁ u₂ v₂ k : ℚ) :
    wdim (u₁ + u₂ - k) (v₁ + v₂) = wdim u₁ v₁ + wdim u₂ v₂ - k := by
  unfold wdim
  ring

/-- Trivial (disjoint) case: `wdim` is additive on orthogonal factors.
    thm:cdim-orthogonal-amalgamated-wdim -/
theorem wdim_amalgamated_trivial (u₁ v₁ u₂ v₂ : ℚ) :
    wdim (u₁ + u₂) (v₁ + v₂) = wdim u₁ v₁ + wdim u₂ v₂ := by
  unfold wdim
  ring

/-- Paper package: orthogonal amalgamated `wdim` formula.
    thm:cdim-orthogonal-amalgamated-wdim -/
theorem paper_cdim_orthogonal_amalgamated_wdim :
    (∀ u v : ℚ, wdim u v = u + v / 2) ∧
    wdim 0 0 = 0 ∧
    (∀ u₁ v₁ u₂ v₂ k : ℚ,
      wdim (u₁ + u₂ - k) (v₁ + v₂) = wdim u₁ v₁ + wdim u₂ v₂ - k) ∧
    (∀ u₁ v₁ u₂ v₂ : ℚ,
      wdim (u₁ + u₂) (v₁ + v₂) = wdim u₁ v₁ + wdim u₂ v₂) ∧
    wdim (2 + 1 - 1) (4 + 2) = wdim 2 4 + wdim 1 2 - 1 := by
  refine ⟨wdim_u_linear, wdim_zero_zero, wdim_amalgamated,
          wdim_amalgamated_trivial, ?_⟩
  exact wdim_amalgamated 2 4 1 2 1

end Omega.CircleDimension
