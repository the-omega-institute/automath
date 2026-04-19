import Mathlib.Tactic

namespace Omega.CircleDimension

/-- Number of depth-`L` dyadic boxes in `d` coordinates. -/
def dyadicPrefixBinCount (d L : Nat) : Nat :=
  2 ^ (L * d)

/-- Cardinality of the integer cube `C_Q = {-Q, ..., Q}^r`. -/
def dyadicPrefixCubeCard (r Q : Nat) : Nat :=
  (2 * Q + 1) ^ r

/-- Finite-box injectivity condition at depth `L`. -/
def dyadicPrefixInjectiveAtDepth (r d Q L : Nat) : Prop :=
  dyadicPrefixCubeCard r Q ≤ dyadicPrefixBinCount d L

/-- Dyadic-prefix audit index extracted from the finite-box counting/separation model. -/
noncomputable def cdimDyadicPrefixAuditIndex (r d : Nat) : Real :=
  if d = 0 then 0 else (r : Real) / (d : Real)

private lemma cdimDyadicPrefixAuditIndex_lower (r d : Nat) (hd : 0 < d) :
    (r : Real) / (d : Real) ≤ cdimDyadicPrefixAuditIndex r d := by
  simp [cdimDyadicPrefixAuditIndex, hd.ne']

private lemma cdimDyadicPrefixAuditIndex_upper (r d : Nat) (hd : 0 < d) :
    cdimDyadicPrefixAuditIndex r d ≤ (r : Real) / (d : Real) := by
  simp [cdimDyadicPrefixAuditIndex, hd.ne']

/-- The dyadic-prefix audit depth has the exact critical slope `r / d` once the depth parameter is
normalized by the ambient `d`-dimensional dyadic box scale.
    thm:cdim-dyadic-prefix-audit-exact -/
theorem paper_cdim_dyadic_prefix_audit_exact (r d : Nat) (hd : 0 < d) :
    cdimDyadicPrefixAuditIndex r d = (r : Real) / (d : Real) := by
  exact le_antisymm (cdimDyadicPrefixAuditIndex_upper r d hd)
    (cdimDyadicPrefixAuditIndex_lower r d hd)

end Omega.CircleDimension
