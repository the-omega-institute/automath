import Mathlib.Tactic
import Omega.CircleDimension.SignedCircleDimension

namespace Omega.CircleDimension

/-- The unit contribution in an audited realization is the circle dimension of the unit part. -/
abbrev auditedRealizationUnitPart (u finiteTorsion : Nat) : ℚ :=
  circleDim u finiteTorsion

/-- The positive-orthant quotient contributes only half of its circle dimension. -/
abbrev auditedRealizationQuotientPart (v : Nat) : ℚ :=
  halfCircleDim v 0

/-- Bookkeeping decomposition of the signed orthant dimension into unit and quotient parts. -/
def auditedRealizationRank (u v finiteTorsion : Nat) : ℚ :=
  auditedRealizationUnitPart u finiteTorsion + auditedRealizationQuotientPart v

theorem auditedRealizationUnitPart_mono {u₁ u₂ finiteTorsion : Nat} (h : u₁ ≤ u₂) :
    auditedRealizationUnitPart u₁ finiteTorsion ≤ auditedRealizationUnitPart u₂ finiteTorsion := by
  unfold auditedRealizationUnitPart
  exact_mod_cast (circleDim_mono (t := finiteTorsion) h)

theorem auditedRealizationQuotientPart_mono {v₁ v₂ : Nat} (h : v₁ ≤ v₂) :
    auditedRealizationQuotientPart v₁ ≤ auditedRealizationQuotientPart v₂ := by
  unfold auditedRealizationQuotientPart
  exact halfCircleDim_mono (t := 0) h

theorem auditedRealizationRank_mono {u₁ u₂ v₁ v₂ finiteTorsion : Nat}
    (hu : u₁ ≤ u₂) (hv : v₁ ≤ v₂) :
    auditedRealizationRank u₁ v₁ finiteTorsion ≤ auditedRealizationRank u₂ v₂ finiteTorsion := by
  exact add_le_add
    (auditedRealizationUnitPart_mono (finiteTorsion := finiteTorsion) hu)
    (auditedRealizationQuotientPart_mono hv)

theorem cdimSignedOrthant_mono {u₁ u₂ v₁ v₂ finiteTorsion : Nat}
    (hu : u₁ ≤ u₂) (hv : v₁ ≤ v₂) :
    cdimSignedOrthant u₁ v₁ finiteTorsion ≤ cdimSignedOrthant u₂ v₂ finiteTorsion := by
  simpa [auditedRealizationRank, cdimSignedOrthant, cdimSigned] using
    auditedRealizationRank_mono (finiteTorsion := finiteTorsion) hu hv

/-- Orthants with budget exactly `(a, b)` attain the signed-circle lower bound in closed form.
    thm:cdim-audited-realization-budget-lower-bound -/
theorem paper_cdim_audited_realization_budget_attained_on_orthant
    (a b finiteTorsion : Nat) :
    cdimSignedOrthant a b finiteTorsion = (a : ℚ) + (b : ℚ) / 2 :=
  (paper_cdim_signed_orthant_closed.1 a b finiteTorsion)

/-- Any audited realization whose unit and quotient ranks fit inside budgets `a` and `b`
    has signed circle dimension at most `a + b/2`.
    thm:cdim-audited-realization-budget-lower-bound -/
theorem paper_cdim_audited_realization_budget_lower_bound
    (u v finiteTorsion a b : Nat) (hUnits : u ≤ a) (hQuot : v ≤ b) :
    cdimSignedOrthant u v finiteTorsion ≤ (a : ℚ) + (b : ℚ) / 2 := by
  have hmono :
      cdimSignedOrthant u v finiteTorsion ≤ cdimSignedOrthant a b finiteTorsion :=
    cdimSignedOrthant_mono (finiteTorsion := finiteTorsion) hUnits hQuot
  simpa [paper_cdim_audited_realization_budget_attained_on_orthant] using hmono

end Omega.CircleDimension
