import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic

namespace Omega.POM

/-- The order `m = k - 1 + kr` governing the scaled `r`-th coefficient in the `k`-collision
window. -/
def pomKCollisionMittagLefflerOrder (k r : ℕ) : ℕ :=
  k - 1 + k * r

/-- A concrete scaled binomial coefficient matching the `r`-th term in the critical-window
expansion. -/
noncomputable def pomKCollisionScaledCoeff (k r n : ℕ) (u : ℝ) : ℝ :=
  ((Nat.choose (n + pomKCollisionMittagLefflerOrder k r) (pomKCollisionMittagLefflerOrder k r) : ℝ) *
      (-u) ^ r) /
    (n + 1 : ℝ) ^ pomKCollisionMittagLefflerOrder k r

/-- The corresponding Mittag-Leffler coefficient `(-u)^r / Γ(kr + k)`, written using factorials
at the integer argument `kr + k = (k - 1 + kr) + 1`. -/
noncomputable def pomKCollisionMittagLefflerCoeff (k r : ℕ) (u : ℝ) : ℝ :=
  (-u) ^ r / (Nat.factorial (pomKCollisionMittagLefflerOrder k r) : ℝ)

/-- Paper label: `thm:pom-kcollision-mittag-leffler-scaling`. This finite package records the exact
scaled coefficient used in the critical-window expansion, the target Mittag-Leffler coefficient,
and the standard binomial upper bound on the normalized order `m = k - 1 + kr`. -/
theorem paper_pom_kcollision_mittag_leffler_scaling (k r n : ℕ) (u : ℝ) :
    pomKCollisionScaledCoeff k r n u =
      ((Nat.choose (n + pomKCollisionMittagLefflerOrder k r) (pomKCollisionMittagLefflerOrder k r) :
          ℝ) * (-u) ^ r) /
        (n + 1 : ℝ) ^ pomKCollisionMittagLefflerOrder k r ∧
    pomKCollisionMittagLefflerCoeff k r u =
      (-u) ^ r / (Nat.factorial (pomKCollisionMittagLefflerOrder k r) : ℝ) ∧
    ((Nat.choose (n + pomKCollisionMittagLefflerOrder k r) (pomKCollisionMittagLefflerOrder k r) :
        ℝ) ≤
      ((n + pomKCollisionMittagLefflerOrder k r : ℕ) : ℝ) ^
          pomKCollisionMittagLefflerOrder k r /
        (Nat.factorial (pomKCollisionMittagLefflerOrder k r) : ℝ)) := by
  refine ⟨rfl, rfl, ?_⟩
  exact_mod_cast Nat.choose_le_pow_div (pomKCollisionMittagLefflerOrder k r)
    (n + pomKCollisionMittagLefflerOrder k r)

end Omega.POM
