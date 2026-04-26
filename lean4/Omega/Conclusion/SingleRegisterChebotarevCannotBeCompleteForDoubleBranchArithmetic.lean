import Omega.Folding.FoldGaugeAnomalyP10P9ChebotarevIndependence

namespace Omega.Conclusion

/-- The first-register certificate only inspects the `P10` branch. -/
def conclusion_single_register_chebotarev_cannot_be_complete_for_double_branch_arithmetic_firstRegisterCertificate
    (cert : Fin 10 → ℕ) : Fin 10 × Fin 9 → ℕ :=
  fun x => cert x.1

/-- The positive-density ambiguity lives entirely in the `P9` branch. -/
def conclusion_single_register_chebotarev_cannot_be_complete_for_double_branch_arithmetic_otherFactorDensity :
    ℚ :=
  Omega.Folding.fold_gauge_anomaly_p10_p9_chebotarev_independence_p9_identity_density

/-- Conclusion-level wrapper: the audited `P10/P9` direct-product Chebotarev package has positive
`P9` density, and every certificate that only reads the `P10` register leaves two distinct
`P9` branches indistinguishable. -/
def conclusion_single_register_chebotarev_cannot_be_complete_for_double_branch_arithmetic_jointPackage :
    Prop :=
  let D := Omega.Folding.fold_gauge_anomaly_p10_p9_chebotarev_independence_data
  D.galoisGroupIsDirectProduct ∧
    conclusion_single_register_chebotarev_cannot_be_complete_for_double_branch_arithmetic_otherFactorDensity =
      (1 : ℚ) / Nat.factorial 9

def conclusion_single_register_chebotarev_cannot_be_complete_for_double_branch_arithmetic_positiveAmbiguity :
    Prop :=
  0 <
      conclusion_single_register_chebotarev_cannot_be_complete_for_double_branch_arithmetic_otherFactorDensity ∧
    ∀ cert : Fin 10 → ℕ,
      ∃ x y : Fin 10 × Fin 9,
        x ≠ y ∧
          x.1 = y.1 ∧
          conclusion_single_register_chebotarev_cannot_be_complete_for_double_branch_arithmetic_firstRegisterCertificate
              cert x =
            conclusion_single_register_chebotarev_cannot_be_complete_for_double_branch_arithmetic_firstRegisterCertificate
              cert y ∧
          x.2 ≠ y.2

def conclusion_single_register_chebotarev_cannot_be_complete_for_double_branch_arithmetic_statement :
    Prop :=
  conclusion_single_register_chebotarev_cannot_be_complete_for_double_branch_arithmetic_jointPackage ∧
    conclusion_single_register_chebotarev_cannot_be_complete_for_double_branch_arithmetic_positiveAmbiguity

/-- Paper label:
`thm:conclusion-single-register-chebotarev-cannot-be-complete-for-double-branch-arithmetic`. -/
theorem paper_conclusion_single_register_chebotarev_cannot_be_complete_for_double_branch_arithmetic :
    conclusion_single_register_chebotarev_cannot_be_complete_for_double_branch_arithmetic_statement := by
  rcases Omega.Folding.paper_fold_gauge_anomaly_p10_p9_chebotarev_independence with
    ⟨hDirect, _hP10, hP9, _hJoint, _hJointClosed⟩
  have hOtherPos :
      0 <
        conclusion_single_register_chebotarev_cannot_be_complete_for_double_branch_arithmetic_otherFactorDensity := by
    rw [show conclusion_single_register_chebotarev_cannot_be_complete_for_double_branch_arithmetic_otherFactorDensity =
            Omega.Folding.fold_gauge_anomaly_p10_p9_chebotarev_independence_p9_identity_density
        by rfl]
    rw [hP9]
    norm_num [Nat.factorial]
  refine ⟨?_, ?_⟩
  · exact ⟨hDirect, hP9⟩
  · refine ⟨hOtherPos, ?_⟩
    intro cert
    let x : Fin 10 × Fin 9 := (0, 0)
    let y : Fin 10 × Fin 9 := (0, 1)
    have hSecond : x.2 ≠ y.2 := by
      change (0 : Fin 9) ≠ 1
      decide
    have hDistinct : x ≠ y := by
      intro hxy
      exact hSecond (congrArg Prod.snd hxy)
    exact ⟨x, y, hDistinct, rfl, rfl, hSecond⟩

end Omega.Conclusion
