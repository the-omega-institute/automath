import Mathlib.Tactic

namespace Omega.Conclusion

theorem paper_conclusion_dyadic_boundary_squarefree_prime_register_exponential_lower_bound
    {P Code : Type*} [Fintype P] [Fintype Code] (m n t : ℕ)
    (hP : Fintype.card P = 2 ^ (2 ^ (m * n))) (hCode : Fintype.card Code = 2 ^ t)
    (H : P → Code) (hH : Function.Injective H) : 2 ^ (m * n) ≤ t := by
  have hcard : Fintype.card P ≤ Fintype.card Code :=
    Fintype.card_le_of_injective H hH
  rw [hP, hCode] at hcard
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hcard

end Omega.Conclusion
