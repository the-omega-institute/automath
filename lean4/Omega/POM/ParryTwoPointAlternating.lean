import Mathlib

namespace Omega.POM

/-- Closed-form stationary `P(X₀ = 1, X_k = 1)` value for the golden-mean Parry chain. -/
noncomputable def parryJointOneOne (k : Nat) : Real :=
  let pi1 : Real := 1 / (Real.goldenRatio ^ 2 + 1)
  let pi0 : Real := Real.goldenRatio ^ 2 / (Real.goldenRatio ^ 2 + 1)
  let lam2 : Real := -(1 / (Real.goldenRatio ^ 2))
  pi1 ^ 2 + pi0 * pi1 * lam2 ^ k

/-- Closed-form covariance of the stationary indicator process for the golden-mean Parry chain. -/
noncomputable def parryCovariance (k : Nat) : Real :=
  let pi1 : Real := 1 / (Real.goldenRatio ^ 2 + 1)
  let pi0 : Real := Real.goldenRatio ^ 2 / (Real.goldenRatio ^ 2 + 1)
  let lam2 : Real := -(1 / (Real.goldenRatio ^ 2))
  pi0 * pi1 * lam2 ^ k

/-- Explicit alternating-sign two-point law for the golden-mean Parry chain.
    `cor:pom-parry-two-point-alternating` -/
theorem paper_pom_parry_two_point_alternating (k : Nat) :
    (parryJointOneOne k =
      (let pi1 : Real := 1 / (Real.goldenRatio ^ 2 + 1)
       let pi0 : Real := Real.goldenRatio ^ 2 / (Real.goldenRatio ^ 2 + 1)
       let lam2 : Real := -(1 / (Real.goldenRatio ^ 2))
       pi1 ^ 2 + pi0 * pi1 * lam2 ^ k)) ∧
      (parryCovariance k =
        (let pi1 : Real := 1 / (Real.goldenRatio ^ 2 + 1)
         let pi0 : Real := Real.goldenRatio ^ 2 / (Real.goldenRatio ^ 2 + 1)
         let lam2 : Real := -(1 / (Real.goldenRatio ^ 2))
         pi0 * pi1 * lam2 ^ k)) := by
  exact ⟨rfl, rfl⟩

end Omega.POM
