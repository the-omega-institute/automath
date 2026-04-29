import Mathlib.Tactic
import Omega.CircleDimension.StarZ1sDualExtension
import Omega.Zeta.LocalizedQuotientLedger

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-finite-prime-support-product-phase-ledger-split`. -/
theorem paper_conclusion_finite_prime_support_product_phase_ledger_split
    (S : Finset Nat) (hS : ∀ p ∈ S, Nat.Prime p) :
    let D : Omega.CircleDimension.Z1sDualExtensionData := { S := S }
    D.kernelIsPadicProduct ∧ D.quotientIsCircle ∧ D.circleDimEqOne ∧
      ∀ p, Nat.Prime p →
        ((p ∈ S ↔ Omega.Zeta.localizedIndex S p = 1) ∧
          (p ∉ S ↔ Omega.Zeta.localizedIndex S p = p)) := by
  classical
  let _ := hS
  let D : Omega.CircleDimension.Z1sDualExtensionData := { S := S }
  have hD := Omega.CircleDimension.paper_cdim_star_z1s_dual_extension D
  refine ⟨hD.1, hD.2.1, hD.2.2, ?_⟩
  intro p hp
  exact Omega.Zeta.paper_xi_localized_quotient_index_prime_recovery S hp

end Omega.Conclusion
