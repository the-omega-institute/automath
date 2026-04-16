import Omega.CircleDimension.CircleDim

namespace Omega.CircleDimension

/-- Abstract signed circle dimension:
    full circle dimension for the unit subgroup plus half of the quotient circle dimension.
    prop:cdim-signed-laws -/
def cdimSigned (unitsRank quotientRank unitsTorsion quotientTorsion : Nat) : ℚ :=
  (circleDim unitsRank unitsTorsion : ℚ) + halfCircleDim quotientRank quotientTorsion

/-- Half circle dimension of the group completion of `ℤ^u ⊕ ℕ^v ⊕ F`.
    In this bookkeeping model the finite summand contributes only torsion.
    prop:cdim-signed-orthant-closed -/
def cdimPlusOrthant (u v finiteTorsion : Nat) : ℚ :=
  halfCircleDim (u + v) finiteTorsion

/-- Signed circle dimension of `ℤ^u ⊕ ℕ^v ⊕ F`: the unit subgroup contributes its full
    circle dimension, while the positive orthant quotient contributes half.
    prop:cdim-signed-orthant-closed -/
def cdimSignedOrthant (u v finiteTorsion : Nat) : ℚ :=
  cdimSigned u v finiteTorsion 0

/-- Paper-facing signed-circle-dimension laws: group case, finite-unit case, additivity,
    and finite-extension invariance.
    prop:cdim-signed-laws -/
theorem paper_cdim_signed_laws :
    (∀ unitsRank unitsTorsion : Nat,
      cdimSigned unitsRank 0 unitsTorsion 0 = circleDim unitsRank unitsTorsion) ∧
    (∀ quotientRank unitsTorsion quotientTorsion : Nat,
      cdimSigned 0 quotientRank unitsTorsion quotientTorsion =
        halfCircleDim quotientRank quotientTorsion) ∧
    (∀ u₁ v₁ tu₁ tq₁ u₂ v₂ tu₂ tq₂ : Nat,
      cdimSigned (u₁ + u₂) (v₁ + v₂) (tu₁ + tu₂) (tq₁ + tq₂) =
        cdimSigned u₁ v₁ tu₁ tq₁ + cdimSigned u₂ v₂ tu₂ tq₂) ∧
    (∀ u₁ v₁ tu₁ tq₁ u₂ v₂ tu₂ tq₂ : Nat,
      u₁ = u₂ → v₁ = v₂ →
        cdimSigned u₁ v₁ tu₁ tq₁ = cdimSigned u₂ v₂ tu₂ tq₂) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro unitsRank unitsTorsion
    simp [cdimSigned, halfCircleDim, circleDim]
  · intro quotientRank unitsTorsion quotientTorsion
    simp [cdimSigned]
  · intro u₁ v₁ tu₁ tq₁ u₂ v₂ tu₂ tq₂
    simp [cdimSigned, circleDim_add, halfCircleDim_add]
    ring
  · intro u₁ v₁ tu₁ tq₁ u₂ v₂ tu₂ tq₂ hu hv
    subst hu
    subst hv
    simp [cdimSigned, halfCircleDim, circleDim]

/-- Paper-facing closed form for the signed circle dimension on orthants with a finite
    torsion factor.
    prop:cdim-signed-orthant-closed -/
theorem paper_cdim_signed_orthant_closed :
    (∀ u v finiteTorsion : Nat,
      cdimSignedOrthant u v finiteTorsion = (u : ℚ) + (v : ℚ) / 2) ∧
    (∀ u v finiteTorsion : Nat,
      cdimPlusOrthant u v finiteTorsion = ((u + v : Nat) : ℚ) / 2) := by
  refine ⟨?_, ?_⟩
  · intro u v finiteTorsion
    simp [cdimSignedOrthant, cdimSigned, halfCircleDim, circleDim]
  · intro u v finiteTorsion
    simp [cdimPlusOrthant, halfCircleDim, circleDim]

end Omega.CircleDimension
