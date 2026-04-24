import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- The rank-`r` dyadic address module at depth `n`. -/
abbrev conclusion_leyang_minimal_dyadic_address_rank_two_address_module (r n : ℕ) :=
  Fin r → ZMod (2 ^ n)

/-- A single Lee--Yang branch coset is modeled by an affine translate of the rank-two dyadic
torsion module. -/
abbrev conclusion_leyang_minimal_dyadic_address_rank_two_branch_coset (n : ℕ) :=
  Fin 2 → ZMod (2 ^ n)

/-- Translation by a fixed branch point identifies the rank-two torsion module with the
corresponding Lee--Yang branch coset. -/
def conclusion_leyang_minimal_dyadic_address_rank_two_translate {n : ℕ}
    (P : conclusion_leyang_minimal_dyadic_address_rank_two_branch_coset n) :
    conclusion_leyang_minimal_dyadic_address_rank_two_branch_coset n ≃
      conclusion_leyang_minimal_dyadic_address_rank_two_branch_coset n where
  toFun x := P + x
  invFun x := x - P
  left_inv x := by
    ext i
    simp
  right_inv x := by
    ext i
    simp

/-- Paper label: `cor:conclusion-leyang-minimal-dyadic-address-rank-two`. A surjection from a
rank-`r` dyadic address module onto one Lee--Yang branch coset forces `r ≥ 2`, while rank two is
already sufficient by translating the canonical identification
`E_min[2^n] ≃ (ℤ / 2^nℤ)^2`. -/
theorem paper_conclusion_leyang_minimal_dyadic_address_rank_two
    (n : ℕ) (hn : 1 ≤ n) :
    (∀ r,
        (∃ f :
          conclusion_leyang_minimal_dyadic_address_rank_two_address_module r n →
            conclusion_leyang_minimal_dyadic_address_rank_two_branch_coset n,
          Function.Surjective f) →
          2 ≤ r) ∧
      (∀ P : conclusion_leyang_minimal_dyadic_address_rank_two_branch_coset n,
        ∃ f :
          conclusion_leyang_minimal_dyadic_address_rank_two_address_module 2 n →
            conclusion_leyang_minimal_dyadic_address_rank_two_branch_coset n,
          Function.Bijective f ∧ ∀ x, f x = P + x) := by
  refine ⟨?_, ?_⟩
  · intro r hsurj
    rcases hsurj with ⟨f, hf⟩
    have hcard :
        Fintype.card
            (conclusion_leyang_minimal_dyadic_address_rank_two_branch_coset n) ≤
          Fintype.card
            (conclusion_leyang_minimal_dyadic_address_rank_two_address_module r n) :=
      Fintype.card_le_of_surjective f hf
    have hpows : 2 ^ (2 * n) ≤ 2 ^ (r * n) := by
      simpa [conclusion_leyang_minimal_dyadic_address_rank_two_address_module,
        conclusion_leyang_minimal_dyadic_address_rank_two_branch_coset,
        Fintype.card_fun, ZMod.card, pow_mul, mul_comm, mul_left_comm, mul_assoc] using hcard
    have hmul : 2 * n ≤ r * n :=
      (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hpows
    exact Nat.le_of_mul_le_mul_right hmul (Nat.succ_le_iff.mp hn)
  · intro P
    refine ⟨conclusion_leyang_minimal_dyadic_address_rank_two_translate P, ?_⟩
    refine ⟨
      (conclusion_leyang_minimal_dyadic_address_rank_two_translate P).bijective,
      ?_⟩
    intro x
    rfl

end Omega.Conclusion
