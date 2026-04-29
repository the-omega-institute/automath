import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import Omega.Conclusion.Window6BoundaryZ6TorsorLocalGlobalMismatch

namespace Omega.Conclusion

/-- Paper label:
`thm:conclusion-window6-boundary-address-rigidity-charge-nonuniqueness`.
The boundary address layer is the regular `ZMod 6` torsor; any binary address realizing six states
uses at least three bits; and the independent `18` binary sign choices have cardinality `2^18`. -/
theorem paper_conclusion_window6_boundary_address_rigidity_charge_nonuniqueness :
    Omega.Conclusion.boundary_uplift_is_regular_Z6_torsor ∧
      (∀ B : ℕ, 6 ≤ 2 ^ B → 3 ≤ B) ∧
      Fintype.card (Fin 18 → ZMod 2) = 2 ^ 18 := by
  refine ⟨?_, ?_, ?_⟩
  · exact
      Omega.Conclusion.paper_conclusion_window6_boundary_z6_torsor_local_global_mismatch.1
  · intro B hB
    by_contra hlt
    have hSmall : B < 3 := Nat.lt_of_not_ge hlt
    interval_cases B <;> norm_num at hB
  · rw [Fintype.card_fun, Fintype.card_fin, ZMod.card]

end Omega.Conclusion
