import Mathlib.Tactic
import Omega.SPG.BoundaryGodelFiniteMomentCompleteness
import Omega.SPG.BoundaryGodelMomentReadout

namespace Omega.Conclusion

/-- Concrete data package for recovering a Serrin object from its finite-moment or boundary-code
tower. -/
structure SerrinFiniteMomentGodelTowerRecoveryData where
  conclusion_serrin_finite_moment_godel_tower_recovery_carrier : Type
  conclusion_serrin_finite_moment_godel_tower_recovery_level :
    ℕ → conclusion_serrin_finite_moment_godel_tower_recovery_carrier
  conclusion_serrin_finite_moment_godel_tower_recovery_momentBox :
    conclusion_serrin_finite_moment_godel_tower_recovery_carrier →
      Omega.SPG.MultiIndex → ℚ
  conclusion_serrin_finite_moment_godel_tower_recovery_godelCode :
    conclusion_serrin_finite_moment_godel_tower_recovery_carrier →
      Omega.SPG.BoundaryGodelCode
  conclusion_serrin_finite_moment_godel_tower_recovery_outerApprox :
    ℕ → Set conclusion_serrin_finite_moment_godel_tower_recovery_carrier
  conclusion_serrin_finite_moment_godel_tower_recovery_closureOmega :
    Set conclusion_serrin_finite_moment_godel_tower_recovery_carrier
  conclusion_serrin_finite_moment_godel_tower_recovery_wulffObservable :
    Fin 1 → ℝ
  conclusion_serrin_finite_moment_godel_tower_recovery_normalizedObservable :
    Fin 1 → ℝ
  conclusion_serrin_finite_moment_godel_tower_recovery_momentReadout :
    ∀ u v,
      conclusion_serrin_finite_moment_godel_tower_recovery_godelCode u =
          conclusion_serrin_finite_moment_godel_tower_recovery_godelCode v →
        conclusion_serrin_finite_moment_godel_tower_recovery_momentBox u =
          conclusion_serrin_finite_moment_godel_tower_recovery_momentBox v
  conclusion_serrin_finite_moment_godel_tower_recovery_momentComplete :
    Function.Injective conclusion_serrin_finite_moment_godel_tower_recovery_momentBox
  conclusion_serrin_finite_moment_godel_tower_recovery_outerApprox_exact :
    ∀ m,
      conclusion_serrin_finite_moment_godel_tower_recovery_outerApprox m =
        {conclusion_serrin_finite_moment_godel_tower_recovery_level m}
  conclusion_serrin_finite_moment_godel_tower_recovery_nested :
    ∀ m,
      conclusion_serrin_finite_moment_godel_tower_recovery_outerApprox (m + 1) ⊆
        conclusion_serrin_finite_moment_godel_tower_recovery_outerApprox m
  conclusion_serrin_finite_moment_godel_tower_recovery_closure_exact :
    conclusion_serrin_finite_moment_godel_tower_recovery_closureOmega =
      {u |
        ∀ m,
          u ∈ conclusion_serrin_finite_moment_godel_tower_recovery_outerApprox m}
  conclusion_serrin_finite_moment_godel_tower_recovery_volume_normalized :
    conclusion_serrin_finite_moment_godel_tower_recovery_normalizedObservable =
      conclusion_serrin_finite_moment_godel_tower_recovery_wulffObservable

/-- Statement extracted from the finite-moment/boundary-code recovery tower. -/
def SerrinFiniteMomentGodelTowerRecoveryStatement
    (D : SerrinFiniteMomentGodelTowerRecoveryData) : Prop :=
  (∀ m,
      {u |
          D.conclusion_serrin_finite_moment_godel_tower_recovery_momentBox u =
            D.conclusion_serrin_finite_moment_godel_tower_recovery_momentBox
              (D.conclusion_serrin_finite_moment_godel_tower_recovery_level m)} =
        D.conclusion_serrin_finite_moment_godel_tower_recovery_outerApprox m) ∧
    (∀ m,
      {u |
          D.conclusion_serrin_finite_moment_godel_tower_recovery_godelCode u =
            D.conclusion_serrin_finite_moment_godel_tower_recovery_godelCode
              (D.conclusion_serrin_finite_moment_godel_tower_recovery_level m)} =
        D.conclusion_serrin_finite_moment_godel_tower_recovery_outerApprox m) ∧
    (∀ m,
      D.conclusion_serrin_finite_moment_godel_tower_recovery_outerApprox (m + 1) ⊆
        D.conclusion_serrin_finite_moment_godel_tower_recovery_outerApprox m) ∧
    D.conclusion_serrin_finite_moment_godel_tower_recovery_closureOmega =
      {u |
        ∀ m,
          u ∈ D.conclusion_serrin_finite_moment_godel_tower_recovery_outerApprox m} ∧
    D.conclusion_serrin_finite_moment_godel_tower_recovery_normalizedObservable =
      D.conclusion_serrin_finite_moment_godel_tower_recovery_wulffObservable

/-- Paper label: `thm:conclusion-serrin-finite-moment-godel-tower-recovery`. At each dyadic level
the finite-moment box and the boundary Gödel code both recover the same approximant, the nested
outer approximations intersect to `closure Ω`, and volume normalization fixes the Wulff
observable. -/
theorem paper_conclusion_serrin_finite_moment_godel_tower_recovery
    (D : SerrinFiniteMomentGodelTowerRecoveryData) :
    SerrinFiniteMomentGodelTowerRecoveryStatement D := by
  have hCodeComplete :
      Function.Injective D.conclusion_serrin_finite_moment_godel_tower_recovery_godelCode :=
    Omega.SPG.paper_spg_boundary_godel_finite_moment_completeness
      D.conclusion_serrin_finite_moment_godel_tower_recovery_godelCode
      D.conclusion_serrin_finite_moment_godel_tower_recovery_momentBox
      D.conclusion_serrin_finite_moment_godel_tower_recovery_momentReadout
      D.conclusion_serrin_finite_moment_godel_tower_recovery_momentComplete
  refine ⟨?_, ?_, D.conclusion_serrin_finite_moment_godel_tower_recovery_nested,
    D.conclusion_serrin_finite_moment_godel_tower_recovery_closure_exact,
    D.conclusion_serrin_finite_moment_godel_tower_recovery_volume_normalized⟩
  · intro m
    ext u
    constructor
    · intro hu
      have hEq :
          u = D.conclusion_serrin_finite_moment_godel_tower_recovery_level m :=
        D.conclusion_serrin_finite_moment_godel_tower_recovery_momentComplete hu
      rw [D.conclusion_serrin_finite_moment_godel_tower_recovery_outerApprox_exact m]
      simp [hEq]
    · intro hu
      rw [D.conclusion_serrin_finite_moment_godel_tower_recovery_outerApprox_exact m] at hu
      have hEq :
          u = D.conclusion_serrin_finite_moment_godel_tower_recovery_level m := by
        simp at hu
        exact hu
      simp [hEq]
  · intro m
    ext u
    constructor
    · intro hu
      have hEq :
          u = D.conclusion_serrin_finite_moment_godel_tower_recovery_level m :=
        hCodeComplete hu
      rw [D.conclusion_serrin_finite_moment_godel_tower_recovery_outerApprox_exact m]
      simp [hEq]
    · intro hu
      rw [D.conclusion_serrin_finite_moment_godel_tower_recovery_outerApprox_exact m] at hu
      have hEq :
          u = D.conclusion_serrin_finite_moment_godel_tower_recovery_level m := by
        simp at hu
        exact hu
      simp [hEq]

end Omega.Conclusion
