import Mathlib.Tactic
import Omega.POM.OrderSpatialization
import Omega.POM.RCRTEpsilon

namespace Omega.POM

/-- Concrete quantile-budget package: the `(\mathrm{RCRT}_\varepsilon)` certificate controls the
bad-event probability, while the CRT side condition `P > 2 B` gives exact residue reconstruction
and order recovery on the good interval `[-B, B]`. -/
def pom_prime_register_quantile_budget_statement : Prop :=
  ∀ {m : ℕ} {eps : ℝ}, 0 < eps → eps < 1 →
    ∀ {X Y : ℤ} {B P : ℕ} (reconstruct : ℤ → ℤ),
      |Y| ≤ pomResidualBudget m X →
      pomBadEventMass Y B ≤ eps →
      P > 2 * B →
      (∀ {z : ℤ}, |z| ≤ B → reconstruct (z % P) = z) →
      pomEpsSoundRewriteCertificate m eps X Y B P reconstruct ∧
        ∀ {x y : ℤ}, |x| ≤ B → |y| ≤ B →
          ((x % P : ℤ) = y % P ↔ x = y) ∧
            (reconstruct (x % P) ≤ reconstruct (y % P) ↔ x ≤ y)

/-- Paper label: `cor:pom-prime-register-quantile-budget`. -/
theorem paper_pom_prime_register_quantile_budget :
    pom_prime_register_quantile_budget_statement := by
  intro m eps hEpsPos hEpsLt X Y B P reconstruct hDom hTail hP hRec
  refine ⟨paper_pom_rcrt_epsilon hEpsPos hEpsLt reconstruct hDom hTail hP hRec, ?_⟩
  intro x y hx hy
  exact paper_pom_order_spatialization B P reconstruct hP hRec hx hy

end Omega.POM
