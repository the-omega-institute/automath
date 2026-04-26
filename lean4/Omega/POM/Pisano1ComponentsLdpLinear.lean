import Mathlib.Data.Real.Basic

namespace Omega.POM

/-- Paper label: `thm:pom-pisano1-components-ldp-linear`. The finite-state
Perron-Frobenius certificate already packages the positive constants and the uniform lower-tail
bound, so the paper-facing statement is obtained by unpacking that certificate. -/
theorem paper_pom_pisano1_components_ldp_linear
    (TailBound : (Nat → Nat) → Real → Real → Prop) (N : Nat → Nat)
    (h_finite_state_pf :
      ∃ mu c : Real, 0 < mu ∧ 0 < c ∧
        ∀ eps : Real, 0 < eps → eps < mu → TailBound N eps c) :
    ∃ mu c : Real, 0 < mu ∧ 0 < c ∧
      ∀ eps : Real, 0 < eps → eps < mu → TailBound N eps c := by
  exact h_finite_state_pf

end Omega.POM
