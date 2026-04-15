import Omega.CircleDimension.CircleDim

namespace Omega.CircleDimension

/-- Half circle dimension of the group completion of `ℤ^u ⊕ ℕ^v ⊕ F`.
    In this bookkeeping model the finite summand contributes only torsion.
    prop:cdim-signed-orthant-closed -/
def cdimPlusOrthant (u v finiteTorsion : Nat) : ℚ :=
  halfCircleDim (u + v) finiteTorsion

/-- Signed circle dimension of `ℤ^u ⊕ ℕ^v ⊕ F`: the unit subgroup contributes its full
    circle dimension, while the positive orthant quotient contributes half.
    prop:cdim-signed-orthant-closed -/
def cdimSignedOrthant (u v finiteTorsion : Nat) : ℚ :=
  (circleDim u finiteTorsion : ℚ) + halfCircleDim v 0

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
    simp [cdimSignedOrthant, halfCircleDim, circleDim]
  · intro u v finiteTorsion
    simp [cdimPlusOrthant, halfCircleDim, circleDim]

end Omega.CircleDimension
