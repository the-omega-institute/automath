import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-godel-tate-badic-prefix-tree`.
Digits bounded by `M < B` inject into the usual base-`B` digit model; the level and tail
cardinalities are the standard cardinalities of function spaces over `Fin`. -/
theorem paper_conclusion_godel_tate_badic_prefix_tree (M B k j : Nat) (hB : M < B)
    (hj : j ≤ k) :
    (∀ a b : Fin k → Fin (M + 1),
        (∑ t : Fin k, (a t : Nat) * B ^ (t : Nat)) =
          (∑ t : Fin k, (b t : Nat) * B ^ (t : Nat)) →
        a = b) ∧
      Fintype.card (Fin k → Fin (M + 1)) = (M + 1) ^ k ∧
        Fintype.card (Fin (k - j) → Fin (M + 1)) = (M + 1) ^ (k - j) := by
  have _hj : j ≤ k := hj
  refine ⟨?_, ?_, ?_⟩
  · intro a b hsum
    have hMB : M + 1 ≤ B := Nat.succ_le_of_lt hB
    let castDigit : Fin (M + 1) → Fin B := fun x => ⟨x, lt_of_lt_of_le x.isLt hMB⟩
    have hencoded :
        finFunctionFinEquiv (fun t : Fin k => castDigit (a t)) =
          finFunctionFinEquiv (fun t : Fin k => castDigit (b t)) := by
      apply Fin.ext
      rw [finFunctionFinEquiv_apply, finFunctionFinEquiv_apply]
      simpa [castDigit] using hsum
    have hdigits :
        (fun t : Fin k => castDigit (a t)) = (fun t : Fin k => castDigit (b t)) :=
      finFunctionFinEquiv.injective hencoded
    ext t
    have ht := congrFun hdigits t
    simpa [castDigit] using congrArg Fin.val ht
  · rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  · rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

end Omega.Conclusion
