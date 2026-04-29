import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic
import Omega.Core.Word

open scoped BigOperators

namespace Omega.Conclusion

abbrev conclusion_leyang_lattes_hypercube_exact_form_zero_curvature_vertex (k : Nat) :=
  Omega.Word (2 * k)

def conclusion_leyang_lattes_hypercube_exact_form_zero_curvature_setTrue {k : Nat}
    (i : Fin (2 * k))
    (x : conclusion_leyang_lattes_hypercube_exact_form_zero_curvature_vertex k) :
    conclusion_leyang_lattes_hypercube_exact_form_zero_curvature_vertex k :=
  fun j => if j = i then true else x j

noncomputable def conclusion_leyang_lattes_hypercube_exact_form_zero_curvature_potential
    {k : Nat} (weight : Fin (2 * k) → Real)
    (x : conclusion_leyang_lattes_hypercube_exact_form_zero_curvature_vertex k) : Real :=
  ∑ i, if x i then weight i else 0

noncomputable def conclusion_leyang_lattes_hypercube_exact_form_zero_curvature_increment
    {k : Nat} (weight : Fin (2 * k) → Real) (i : Fin (2 * k))
    (x : conclusion_leyang_lattes_hypercube_exact_form_zero_curvature_vertex k) : Real :=
  conclusion_leyang_lattes_hypercube_exact_form_zero_curvature_potential weight
      (conclusion_leyang_lattes_hypercube_exact_form_zero_curvature_setTrue i x) -
    conclusion_leyang_lattes_hypercube_exact_form_zero_curvature_potential weight x

noncomputable def conclusion_leyang_lattes_hypercube_exact_form_zero_curvature_boundary
    {k : Nat} (weight : Fin (2 * k) → Real) (i j : Fin (2 * k))
    (x : conclusion_leyang_lattes_hypercube_exact_form_zero_curvature_vertex k) : Real :=
  conclusion_leyang_lattes_hypercube_exact_form_zero_curvature_increment weight i x +
    conclusion_leyang_lattes_hypercube_exact_form_zero_curvature_increment weight j
      (conclusion_leyang_lattes_hypercube_exact_form_zero_curvature_setTrue i x) -
    conclusion_leyang_lattes_hypercube_exact_form_zero_curvature_increment weight i
      (conclusion_leyang_lattes_hypercube_exact_form_zero_curvature_setTrue j x) -
    conclusion_leyang_lattes_hypercube_exact_form_zero_curvature_increment weight j x

lemma conclusion_leyang_lattes_hypercube_exact_form_zero_curvature_increment_eq
    {k : Nat} (weight : Fin (2 * k) → Real) (i : Fin (2 * k))
    (x : conclusion_leyang_lattes_hypercube_exact_form_zero_curvature_vertex k)
    (hx : x i = false) :
    conclusion_leyang_lattes_hypercube_exact_form_zero_curvature_increment weight i x =
      weight i := by
  classical
  unfold conclusion_leyang_lattes_hypercube_exact_form_zero_curvature_increment
    conclusion_leyang_lattes_hypercube_exact_form_zero_curvature_potential
    conclusion_leyang_lattes_hypercube_exact_form_zero_curvature_setTrue
  rw [← Finset.sum_sub_distrib]
  calc
    (∑ j : Fin (2 * k),
        ((if (if j = i then true else x j) then weight j else 0) -
          if x j then weight j else 0)) =
        ∑ j : Fin (2 * k), if j = i then weight i else 0 := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          by_cases hji : j = i
          · subst j
            simp [hx]
          · simp [hji]
    _ = weight i := by simp

/-- Paper label: `prop:conclusion-leyang-lattes-hypercube-exact-form-zero-curvature`.
The Boolean `2k`-cube potential has the declared coordinate increments on oriented
zero-to-one edges, and the square boundary sum vanishes by telescoping. -/
theorem paper_conclusion_leyang_lattes_hypercube_exact_form_zero_curvature {k : Nat}
    (weight : Fin (2 * k) → Real) :
    (∀ (x : conclusion_leyang_lattes_hypercube_exact_form_zero_curvature_vertex k)
        (i : Fin (2 * k)),
      x i = false →
        conclusion_leyang_lattes_hypercube_exact_form_zero_curvature_increment weight i x =
          weight i) ∧
      (∀ (x : conclusion_leyang_lattes_hypercube_exact_form_zero_curvature_vertex k)
          (i j : Fin (2 * k)),
        i ≠ j →
          x i = false →
          x j = false →
            conclusion_leyang_lattes_hypercube_exact_form_zero_curvature_boundary weight i j x =
              0) := by
  refine ⟨?_, ?_⟩
  · intro x i hx
    exact conclusion_leyang_lattes_hypercube_exact_form_zero_curvature_increment_eq weight i x hx
  · intro x i j hij hxi hxj
    have hi_after_j :
        (conclusion_leyang_lattes_hypercube_exact_form_zero_curvature_setTrue j x) i = false := by
      simp [conclusion_leyang_lattes_hypercube_exact_form_zero_curvature_setTrue, hij, hxi]
    have hj_after_i :
        (conclusion_leyang_lattes_hypercube_exact_form_zero_curvature_setTrue i x) j = false := by
      have hji : j ≠ i := fun h => hij h.symm
      simp [conclusion_leyang_lattes_hypercube_exact_form_zero_curvature_setTrue, hji, hxj]
    rw [conclusion_leyang_lattes_hypercube_exact_form_zero_curvature_boundary,
      conclusion_leyang_lattes_hypercube_exact_form_zero_curvature_increment_eq weight i x hxi,
      conclusion_leyang_lattes_hypercube_exact_form_zero_curvature_increment_eq weight j
        (conclusion_leyang_lattes_hypercube_exact_form_zero_curvature_setTrue i x) hj_after_i,
      conclusion_leyang_lattes_hypercube_exact_form_zero_curvature_increment_eq weight i
        (conclusion_leyang_lattes_hypercube_exact_form_zero_curvature_setTrue j x) hi_after_j,
      conclusion_leyang_lattes_hypercube_exact_form_zero_curvature_increment_eq weight j x hxj]
    ring

end Omega.Conclusion
