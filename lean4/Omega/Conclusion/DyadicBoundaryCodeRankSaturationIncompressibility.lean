import Mathlib.Data.Fintype.Card

set_option linter.unusedVariables false

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-dyadic-boundary-code-rank-saturation-incompressibility`.
An injective boundary code from the dyadic polycube family into a `t`-bit code has enough target
states for all polycubes; strict monotonicity of powers of two converts the cardinal comparison
into the exponent lower bound. -/
theorem paper_conclusion_dyadic_boundary_code_rank_saturation_incompressibility
    (m n t : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (P Code : Type) [Fintype P] [Fintype Code]
    (hP : Fintype.card P = 2 ^ (2 ^ (m * n))) (hCode : Fintype.card Code = 2 ^ t)
    (C : P → Code) (hC : Function.Injective C) : 2 ^ (m * n) ≤ t := by
  have hcard : Fintype.card P ≤ Fintype.card Code :=
    Fintype.card_le_of_injective C hC
  have hpow : 2 ^ (2 ^ (m * n)) ≤ 2 ^ t := by
    simpa [hP, hCode] using hcard
  exact (Nat.pow_le_pow_iff_right Nat.one_lt_two).mp hpow

end Omega.Conclusion
