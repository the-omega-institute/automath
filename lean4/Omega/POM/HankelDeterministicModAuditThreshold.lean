import Mathlib.Tactic

namespace Omega.POM

/-- Concrete audit data after clearing denominators by the minimal integrality factor `N_*`. The
integer matrix `auditResidual` plays the role of the cleared residual `F`. -/
structure pom_hankel_deterministic_mod_audit_threshold_data (d : Nat) where
  minimalFactor : Nat
  primeProduct : Nat
  infinityBound : Nat
  auditResidual : Fin d → Fin d → Int
  primeProductLarge : primeProduct > 2 * infinityBound
  residualDivisible : ∀ i j, (primeProduct : Int) ∣ auditResidual i j
  residualBound : ∀ i j, |auditResidual i j| ≤ infinityBound

/-- The residual already cleared by the minimal integrality factor `N_*`. -/
def pom_hankel_deterministic_mod_audit_threshold_cleared_residual {d : Nat}
    (h : pom_hankel_deterministic_mod_audit_threshold_data d) (i j : Fin d) : Int :=
  (h.minimalFactor : Int) * h.auditResidual i j

/-- If the product of audited primes is larger than twice the infinity norm of the cleared
residual, every entry vanishes. -/
def pom_hankel_deterministic_mod_audit_threshold_statement (d : Nat)
    (h : pom_hankel_deterministic_mod_audit_threshold_data d) : Prop :=
  (∀ i j, h.auditResidual i j = 0) ∧
    ∀ i j, pom_hankel_deterministic_mod_audit_threshold_cleared_residual h i j = 0

/-- Paper label: `thm:pom-hankel-deterministic-mod-audit-threshold`. -/
theorem paper_pom_hankel_deterministic_mod_audit_threshold (d : Nat)
    (h : pom_hankel_deterministic_mod_audit_threshold_data d) :
    pom_hankel_deterministic_mod_audit_threshold_statement d h := by
  have hentry_zero : ∀ i j, h.auditResidual i j = 0 := by
    intro i j
    have hbound_lt : h.infinityBound < h.primeProduct := by
      have hle : h.infinityBound ≤ 2 * h.infinityBound := by
        omega
      exact lt_of_le_of_lt hle h.primeProductLarge
    have hlt :
        |h.auditResidual i j| < h.primeProduct := by
      have hprime : (h.infinityBound : Int) < h.primeProduct := by
        exact_mod_cast hbound_lt
      exact lt_of_le_of_lt (h.residualBound i j) hprime
    exact Int.eq_zero_of_abs_lt_dvd (h.residualDivisible i j) hlt
  refine ⟨hentry_zero, ?_⟩
  intro i j
  simp [pom_hankel_deterministic_mod_audit_threshold_cleared_residual, hentry_zero i j]

end Omega.POM
