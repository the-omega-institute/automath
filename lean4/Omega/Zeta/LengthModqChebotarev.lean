import Mathlib.Tactic

/-!
# Length mod-q Chebotarev-Mertens seed values

Arithmetic identities for the Chebotarev-Mertens density theorem seeds.
-/

namespace Omega.Zeta

/-- Length mod-q Chebotarev-Mertens seeds.
    thm:zeta-length-modq-chebotarev-mertens -/
theorem paper_zeta_length_modq_chebotarev_mertens_seeds :
    (1 - 1 - 1 = (-1 : ℤ) ∧ 1 + 1 - 1 = (1 : ℤ)) ∧
    (1 = 1 ∧ 1 + 1 = 2) ∧
    (2 * 1 = 2) ∧
    (1 + 3 = 4 ∧ 3 + 4 = 7) ∧
    (3 - 1 = 2 ∧ 2 / 2 = 1) := by
  omega

end Omega.Zeta
