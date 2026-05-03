import Mathlib.Tactic

namespace Omega.Zeta

/-- Pointwise equality of finite Euler atom contributions rewrites the indexed finite sum. -/
lemma xi_finite_euler_primitive_surgery_strict_additivity_sum_congr {ι R : Type*}
    [CommSemiring R] [Fintype ι] (f g : ι → R) (h : ∀ j, f j = g j) :
    Finset.univ.sum f = Finset.univ.sum g := by
  exact Finset.sum_congr rfl (fun j _ => h j)

/-- Paper label: `thm:xi-finite-euler-primitive-surgery-strict-additivity`. -/
theorem paper_xi_finite_euler_primitive_surgery_strict_additivity {ι R : Type*}
    [CommSemiring R] [Fintype ι]
    (primitiveContribution constantContribution atomAtZ atomAtZstar : ι → R) (mult : ι → R)
    (hP : ∀ j, primitiveContribution j = mult j * atomAtZ j)
    (hC : ∀ j, constantContribution j = mult j * atomAtZstar j) :
    Finset.univ.sum primitiveContribution =
        Finset.univ.sum (fun j => mult j * atomAtZ j) ∧
      Finset.univ.sum constantContribution =
        Finset.univ.sum (fun j => mult j * atomAtZstar j) := by
  exact
    ⟨xi_finite_euler_primitive_surgery_strict_additivity_sum_congr
        primitiveContribution (fun j => mult j * atomAtZ j) hP,
      xi_finite_euler_primitive_surgery_strict_additivity_sum_congr
        constantContribution (fun j => mult j * atomAtZstar j) hC⟩

end Omega.Zeta
