import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-stable-add-query-saturation-mul-unit-slice`. -/
theorem paper_xi_stable_add_query_saturation_mul_unit_slice
    (m Qadd Qleft Qright : ℕ)
    (hadd_lower : 2 * m ≤ Qadd) (hadd_upper : Qadd ≤ 2 * m)
    (hleft_lower : m ≤ Qleft) (hleft_upper : Qleft ≤ m)
    (hright_lower : m ≤ Qright) (hright_upper : Qright ≤ m) :
    Qadd = 2 * m ∧ Qleft = m ∧ Qright = m := by
  exact ⟨Nat.le_antisymm hadd_upper hadd_lower,
    Nat.le_antisymm hleft_upper hleft_lower,
    Nat.le_antisymm hright_upper hright_lower⟩

end Omega.Zeta
