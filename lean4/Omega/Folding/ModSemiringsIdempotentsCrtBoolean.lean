import Mathlib

namespace Omega.Folding

/-- The finite subsets of `Fin r` are equivalent to the `0/1` choices on each coordinate, and
there are exactly `2^r` of them.
`cor:fold-mod-semirings-idempotents-crt-boolean` -/
theorem paper_fold_mod_semirings_idempotents_crt_boolean (r : ℕ) :
    ∃ φ : Finset (Fin r) ≃ (Fin r → Bool), Fintype.card (Finset (Fin r)) = 2 ^ r := by
  classical
  let φ : Finset (Fin r) ≃ (Fin r → Bool) :=
    { toFun := fun s i => if i ∈ s then true else false
      invFun := fun f => Finset.univ.filter fun i => f i
      left_inv := by
        intro s
        ext i
        by_cases hi : i ∈ s <;> simp [hi]
      right_inv := by
        intro f
        funext i
        by_cases hi : f i <;> simp [hi] }
  refine ⟨φ, ?_⟩
  simpa using Fintype.card_fun (α := Fin r) (β := Bool)

end Omega.Folding
