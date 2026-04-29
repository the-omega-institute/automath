import Mathlib.Tactic
import Omega.Conclusion.FiberCanonicalRowmotionOrderLaw

namespace Omega.Conclusion

/-- A single posterior readout determines the recovered path-length data; together with the
canonical rowmotion lcm law, it therefore determines the rowmotion order and every predicate
depending only on that order, such as prime-factor membership. -/
def conclusion_single_bias_posterior_determines_rowmotion_order_statement
    {State Posterior : Type} (posterior : State → Posterior) (lengths : State → List Nat)
    (rowOrder : State → Nat) (primeFactor : Nat → Nat → Prop) : Prop :=
  (∀ ⦃s t : State⦄, posterior s = posterior t → lengths s = lengths t) →
    (∀ s : State, rowOrder s = ((lengths s).map fun ell => ell + 2).foldl Nat.lcm 1) →
      ∀ ⦃s t : State⦄, posterior s = posterior t →
        rowOrder s = rowOrder t ∧
          ∀ p : Nat, (primeFactor p (rowOrder s) ↔ primeFactor p (rowOrder t))

/-- Paper label: `cor:conclusion-single-bias-posterior-determines-rowmotion-order`. -/
theorem paper_conclusion_single_bias_posterior_determines_rowmotion_order
    {State Posterior : Type} (posterior : State -> Posterior) (lengths : State -> List Nat)
    (rowOrder : State -> Nat) (primeFactor : Nat -> Nat -> Prop) :
    conclusion_single_bias_posterior_determines_rowmotion_order_statement posterior lengths
      rowOrder primeFactor := by
  intro hposterior_lengths hrow s t hposterior
  let componentOrder : Nat → Nat := fun ell => ell + 2
  have hcomponent : ∀ ell, componentOrder ell = ell + 2 := fun _ => rfl
  have hs_lcm :=
    (paper_conclusion_fiber_canonical_rowmotion_order_law componentOrder (lengths s)
      hcomponent).1
  have ht_lcm :=
    (paper_conclusion_fiber_canonical_rowmotion_order_law componentOrder (lengths t)
      hcomponent).1
  have hlengths : lengths s = lengths t := hposterior_lengths hposterior
  have horder : rowOrder s = rowOrder t := by
    calc
      rowOrder s = ((lengths s).map componentOrder).foldl Nat.lcm 1 := hrow s
      _ = (lengths s).foldl (fun acc ell => Nat.lcm acc (ell + 2)) 1 := hs_lcm
      _ = (lengths t).foldl (fun acc ell => Nat.lcm acc (ell + 2)) 1 := by rw [hlengths]
      _ = ((lengths t).map componentOrder).foldl Nat.lcm 1 := ht_lcm.symm
      _ = rowOrder t := (hrow t).symm
  refine ⟨horder, ?_⟩
  intro p
  rw [horder]

end Omega.Conclusion
