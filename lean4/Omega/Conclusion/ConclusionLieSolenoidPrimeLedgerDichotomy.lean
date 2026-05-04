import Mathlib.Tactic
import Omega.CircleDimension.StarZ1sDualExtension
import Omega.Zeta.LocalizedSolenoidCircleQuotientLifts
import Omega.Zeta.XiCdimLocalizationSolenoidNotSubgroupOrQuotientOfFiniteTorus

namespace Omega.Conclusion

/-- Concrete conclusion package for the prime-ledger solenoid dichotomy at a single prime. The
three clauses record the finite-torus obstruction, the rank-one solenoid extension, and the
one-dimensional rational/circle-dimension ledger with the localized prime index. -/
def conclusion_lie_solenoid_prime_ledger_dichotomy_statement (p : ℕ) : Prop :=
  let S : Finset ℕ := {p}
  let D : Omega.CircleDimension.Z1sDualExtensionData := { S := S }
  (∀ n : ℕ, 1 ≤ n →
      Omega.Zeta.XiCdimLocalizationSolenoidNotSubgroupOrQuotientOfFiniteTorus S n) ∧
    D.kernelIsPadicProduct ∧
      D.quotientIsCircle ∧
        D.circleDimEqOne ∧
          Omega.Zeta.localizedIntegersCircleDimension S = 1 ∧
            (Omega.CircleDimension.circleDim 1 0 : ℚ) = 1 ∧
              (∃! φ : Omega.Zeta.LocalizedCrossHom S S,
                Omega.Zeta.localizedCrossHomScalar φ = p) ∧
                (p ∈ S ↔ Omega.Zeta.localizedIndex S p = 1) ∧
                  (p ∉ S ↔ Omega.Zeta.localizedIndex S p = p)

/-- Paper label: `thm:conclusion-lie-solenoid-prime-ledger-dichotomy`. -/
theorem paper_conclusion_lie_solenoid_prime_ledger_dichotomy (p : ℕ) (hp : Nat.Prime p) :
    conclusion_lie_solenoid_prime_ledger_dichotomy_statement p := by
  let S : Finset ℕ := {p}
  let D : Omega.CircleDimension.Z1sDualExtensionData := { S := S }
  have hDual := Omega.CircleDimension.paper_cdim_star_z1s_dual_extension D
  have hLift := Omega.Zeta.paper_xi_time_part62db_localized_solenoid_circle_quotient_lifts S p hp
  refine ⟨?_, hDual.1, hDual.2.1, hDual.2.2, ?_, ?_, hLift.1, hLift.2.1, hLift.2.2⟩
  · intro n hn
    exact Omega.Zeta.paper_xi_cdim_localization_solenoid_not_subgroup_or_quotient_of_finite_torus
      S n hn
  · rfl
  · norm_num [Omega.CircleDimension.circleDim]

end Omega.Conclusion
