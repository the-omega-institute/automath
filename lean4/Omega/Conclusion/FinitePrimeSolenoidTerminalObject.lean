import Mathlib.Tactic
import Omega.CircleDimension.StarZ1sDualExtension
import Omega.Zeta.LocalizedSolenoidCircleQuotientLifts
import Omega.Zeta.XiCdimLocalizationSolenoidCircleExtensionNonsplit
import Omega.Zeta.XiCdimLocalizationSolenoidNoNontrivialTorusInput

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-finite-prime-solenoid-terminal-object`.
This conclusion-level package wraps the standard finite-prime localized solenoid facts already
formalized elsewhere: the explicit `p`-adic kernel, the visible circle quotient, the unique
localized circle lift, the prime-index readout, the nonsplitting extension step, and the
one-dimensional torus-rigidity obstruction. -/
def conclusion_finite_prime_solenoid_terminal_object_statement : Prop :=
  ∀ (S : Finset ℕ) (_hS : ∀ p ∈ S, Nat.Prime p) (p : ℕ), Nat.Prime p →
    let D : Omega.CircleDimension.Z1sDualExtensionData := { S := S }
    D.kernelIsPadicProduct ∧
      D.quotientIsCircle ∧
      D.circleDimEqOne ∧
      (∃! φ : Omega.Zeta.LocalizedCrossHom S S, Omega.Zeta.localizedCrossHomScalar φ = p) ∧
      ((p ∈ S ↔ Omega.Zeta.localizedIndex S p = 1) ∧
        (p ∉ S ↔ Omega.Zeta.localizedIndex S p = p)) ∧
      Omega.Zeta.xiCdimLocalizationSolenoidNoNontrivialTorusInput S 1 ∧
      ∀ q, Nat.Prime q → q ∉ S →
        Omega.Zeta.XiCdimLocalizationSolenoidCircleExtensionNonsplit S (insert q S)

theorem paper_conclusion_finite_prime_solenoid_terminal_object :
    conclusion_finite_prime_solenoid_terminal_object_statement := by
  intro S _hS p hp
  let D : Omega.CircleDimension.Z1sDualExtensionData := { S := S }
  have hDual := Omega.CircleDimension.paper_cdim_star_z1s_dual_extension D
  have hLift := Omega.Zeta.paper_xi_time_part62db_localized_solenoid_circle_quotient_lifts S p hp
  refine ⟨hDual.1, hDual.2.1, hDual.2.2, hLift.1, hLift.2, ?_, ?_⟩
  · exact Omega.Zeta.paper_xi_cdim_localization_solenoid_no_nontrivial_torus_input S 1
  · intro q _hq _hqNotMem
    exact Omega.Zeta.paper_xi_cdim_localization_solenoid_circle_extension_nonsplit S (insert q S)

end Omega.Conclusion
