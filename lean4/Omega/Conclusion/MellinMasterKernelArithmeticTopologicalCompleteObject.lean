import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Paper label:
`thm:conclusion-mellin-master-kernel-arithmetic-topological-complete-object`. -/
theorem paper_conclusion_mellin_master_kernel_arithmetic_topological_complete_object
    {α : Type*} [Fintype α] (d : α → ℕ) (q : ℕ) :
    (∑ n ∈ Finset.univ.image d, (Nat.card {x : α // d x = n}) * n ^ q) =
      ∑ x : α, d x ^ q := by
  classical
  let f : α → ℕ := fun x => d x ^ q
  calc
    (∑ n ∈ Finset.univ.image d, (Nat.card {x : α // d x = n}) * n ^ q)
        = ∑ n ∈ Finset.univ.image d,
            ∑ x ∈ (Finset.univ.filter fun x : α => d x = n), n ^ q := by
          refine Finset.sum_congr rfl ?_
          intro n _hn
          rw [Finset.sum_const, nsmul_eq_mul]
          congr 1
          simp [Fintype.card_subtype]
    _ = ∑ n ∈ Finset.univ.image d,
            ∑ x ∈ (Finset.univ.filter fun x : α => d x = n), f x := by
          refine Finset.sum_congr rfl ?_
          intro n _hn
          refine Finset.sum_congr rfl ?_
          intro x hx
          exact congrArg (fun y => y ^ q) (Finset.mem_filter.mp hx).2.symm
    _ = ∑ x ∈ (Finset.univ : Finset α), f x := by
          rw [← Finset.sum_fiberwise_of_maps_to
            (s := (Finset.univ : Finset α)) (t := Finset.univ.image d)
            (g := d) (f := f) (fun x hx => Finset.mem_image_of_mem d hx)]
    _ = ∑ x : α, d x ^ q := by
          simp [f]

end Omega.Conclusion
