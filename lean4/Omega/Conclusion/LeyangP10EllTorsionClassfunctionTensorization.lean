import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

noncomputable section

/-- Requested data handle for the finite-product `P10 × LY × ell` tensor model. -/
abbrev conclusion_leyang_p10_ell_torsion_classfunction_tensorization_data := PUnit

/-- The `P10` Frobenius factor. -/
abbrev conclusion_leyang_p10_ell_torsion_classfunction_tensorization_p10_group :=
  Equiv.Perm (Fin 10)

/-- The Lee--Yang cubic Frobenius factor. -/
abbrev conclusion_leyang_p10_ell_torsion_classfunction_tensorization_leyang_group :=
  Equiv.Perm (Fin 3)

/-- A concrete finite good-ell torsion factor. -/
abbrev conclusion_leyang_p10_ell_torsion_classfunction_tensorization_ell_group :=
  Equiv.Perm (Fin 2)

/-- The three-factor product model for the unramified Frobenius classes. -/
abbrev conclusion_leyang_p10_ell_torsion_classfunction_tensorization_joint_group :=
  conclusion_leyang_p10_ell_torsion_classfunction_tensorization_p10_group ×
    (conclusion_leyang_p10_ell_torsion_classfunction_tensorization_leyang_group ×
      conclusion_leyang_p10_ell_torsion_classfunction_tensorization_ell_group)

/-- Uniform finite-group average. -/
def conclusion_leyang_p10_ell_torsion_classfunction_tensorization_average
    {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  𝔼 a, f a

/-- Tensor factorization and centered mixed-moment vanishing for finite uniform averages. -/
def conclusion_leyang_p10_ell_torsion_classfunction_tensorization_statement
    (_D : conclusion_leyang_p10_ell_torsion_classfunction_tensorization_data) : Prop :=
  (∀ f : conclusion_leyang_p10_ell_torsion_classfunction_tensorization_p10_group → ℝ,
      ∀ g : conclusion_leyang_p10_ell_torsion_classfunction_tensorization_leyang_group → ℝ,
      ∀ h : conclusion_leyang_p10_ell_torsion_classfunction_tensorization_ell_group → ℝ,
        conclusion_leyang_p10_ell_torsion_classfunction_tensorization_average
            (fun x : conclusion_leyang_p10_ell_torsion_classfunction_tensorization_joint_group =>
              f x.1 * g x.2.1 * h x.2.2) =
          conclusion_leyang_p10_ell_torsion_classfunction_tensorization_average f *
            conclusion_leyang_p10_ell_torsion_classfunction_tensorization_average g *
              conclusion_leyang_p10_ell_torsion_classfunction_tensorization_average h) ∧
    ∀ f : conclusion_leyang_p10_ell_torsion_classfunction_tensorization_p10_group → ℝ,
      ∀ g : conclusion_leyang_p10_ell_torsion_classfunction_tensorization_leyang_group → ℝ,
      ∀ h : conclusion_leyang_p10_ell_torsion_classfunction_tensorization_ell_group → ℝ,
        conclusion_leyang_p10_ell_torsion_classfunction_tensorization_average
            (fun x : conclusion_leyang_p10_ell_torsion_classfunction_tensorization_joint_group =>
              (f x.1 -
                  conclusion_leyang_p10_ell_torsion_classfunction_tensorization_average f) *
                (g x.2.1 -
                  conclusion_leyang_p10_ell_torsion_classfunction_tensorization_average g) *
                  (h x.2.2 -
                    conclusion_leyang_p10_ell_torsion_classfunction_tensorization_average h)) =
          0

/-- Finite-product averaging factors over the three uniform coordinates. -/
lemma conclusion_leyang_p10_ell_torsion_classfunction_tensorization_factorized_average
    (f : conclusion_leyang_p10_ell_torsion_classfunction_tensorization_p10_group → ℝ)
    (g : conclusion_leyang_p10_ell_torsion_classfunction_tensorization_leyang_group → ℝ)
    (h : conclusion_leyang_p10_ell_torsion_classfunction_tensorization_ell_group → ℝ) :
    conclusion_leyang_p10_ell_torsion_classfunction_tensorization_average
        (fun x : conclusion_leyang_p10_ell_torsion_classfunction_tensorization_joint_group =>
          f x.1 * g x.2.1 * h x.2.2) =
      conclusion_leyang_p10_ell_torsion_classfunction_tensorization_average f *
        conclusion_leyang_p10_ell_torsion_classfunction_tensorization_average g *
          conclusion_leyang_p10_ell_torsion_classfunction_tensorization_average h := by
    let EG : ℝ :=
      conclusion_leyang_p10_ell_torsion_classfunction_tensorization_average g
    let EH : ℝ :=
      conclusion_leyang_p10_ell_torsion_classfunction_tensorization_average h
    calc
      conclusion_leyang_p10_ell_torsion_classfunction_tensorization_average
          (fun x : conclusion_leyang_p10_ell_torsion_classfunction_tensorization_joint_group =>
            f x.1 * g x.2.1 * h x.2.2) =
          conclusion_leyang_p10_ell_torsion_classfunction_tensorization_average
            (fun a : conclusion_leyang_p10_ell_torsion_classfunction_tensorization_p10_group =>
              conclusion_leyang_p10_ell_torsion_classfunction_tensorization_average
                (fun yz :
                    conclusion_leyang_p10_ell_torsion_classfunction_tensorization_leyang_group ×
                      conclusion_leyang_p10_ell_torsion_classfunction_tensorization_ell_group =>
                  f a * g yz.1 * h yz.2)) := by
            simpa [conclusion_leyang_p10_ell_torsion_classfunction_tensorization_average] using
              (Finset.expect_product'
                (s := (Finset.univ :
                  Finset conclusion_leyang_p10_ell_torsion_classfunction_tensorization_p10_group))
                (t := (Finset.univ :
                  Finset
                    (conclusion_leyang_p10_ell_torsion_classfunction_tensorization_leyang_group ×
                      conclusion_leyang_p10_ell_torsion_classfunction_tensorization_ell_group)))
                (f := fun a yz => f a * g yz.1 * h yz.2))
      _ =
          conclusion_leyang_p10_ell_torsion_classfunction_tensorization_average
            (fun a : conclusion_leyang_p10_ell_torsion_classfunction_tensorization_p10_group =>
              (f a * EG) * EH) := by
            refine Finset.expect_congr rfl ?_
            intro a _ha
            calc
              conclusion_leyang_p10_ell_torsion_classfunction_tensorization_average
                  (fun yz :
                      conclusion_leyang_p10_ell_torsion_classfunction_tensorization_leyang_group ×
                        conclusion_leyang_p10_ell_torsion_classfunction_tensorization_ell_group =>
                    f a * g yz.1 * h yz.2) =
                conclusion_leyang_p10_ell_torsion_classfunction_tensorization_average
                  (fun b :
                      conclusion_leyang_p10_ell_torsion_classfunction_tensorization_leyang_group =>
                    conclusion_leyang_p10_ell_torsion_classfunction_tensorization_average
                      (fun c :
                          conclusion_leyang_p10_ell_torsion_classfunction_tensorization_ell_group =>
                        (f a * g b) * h c)) := by
                  simpa [conclusion_leyang_p10_ell_torsion_classfunction_tensorization_average,
                    mul_assoc] using
                    (Finset.expect_product'
                      (s := (Finset.univ :
                        Finset
                          conclusion_leyang_p10_ell_torsion_classfunction_tensorization_leyang_group))
                      (t := (Finset.univ :
                        Finset
                          conclusion_leyang_p10_ell_torsion_classfunction_tensorization_ell_group))
                      (f := fun b c => (f a * g b) * h c))
              _ =
                conclusion_leyang_p10_ell_torsion_classfunction_tensorization_average
                  (fun b :
                      conclusion_leyang_p10_ell_torsion_classfunction_tensorization_leyang_group =>
                    (f a * g b) * EH) := by
                  refine Finset.expect_congr rfl ?_
                  intro b _hb
                  simpa [EH,
                    conclusion_leyang_p10_ell_torsion_classfunction_tensorization_average,
                    mul_assoc, mul_left_comm, mul_comm] using
                    (Finset.expect_mul
                      (s := (Finset.univ :
                        Finset
                          conclusion_leyang_p10_ell_torsion_classfunction_tensorization_ell_group))
                      (f := fun c :
                          conclusion_leyang_p10_ell_torsion_classfunction_tensorization_ell_group =>
                        h c) (a := f a * g b)).symm
              _ = (f a * EG) * EH := by
                  calc
                    conclusion_leyang_p10_ell_torsion_classfunction_tensorization_average
                        (fun b :
                            conclusion_leyang_p10_ell_torsion_classfunction_tensorization_leyang_group =>
                          (f a * g b) * EH) =
                      f a *
                        conclusion_leyang_p10_ell_torsion_classfunction_tensorization_average
                          (fun b :
                              conclusion_leyang_p10_ell_torsion_classfunction_tensorization_leyang_group =>
                            g b * EH) := by
                            simpa [
                              conclusion_leyang_p10_ell_torsion_classfunction_tensorization_average,
                              mul_assoc, mul_left_comm, mul_comm] using
                              (Finset.mul_expect
                                (s := (Finset.univ :
                                  Finset
                                    conclusion_leyang_p10_ell_torsion_classfunction_tensorization_leyang_group))
                                (f := fun b :
                                    conclusion_leyang_p10_ell_torsion_classfunction_tensorization_leyang_group =>
                                  g b * EH) (a := f a)).symm
                    _ = f a * (EG * EH) := by
                          congr 1
                          symm
                          simpa [EG,
                            conclusion_leyang_p10_ell_torsion_classfunction_tensorization_average,
                            mul_assoc, mul_left_comm, mul_comm] using
                            (Finset.expect_mul
                              (s := (Finset.univ :
                                Finset
                                  conclusion_leyang_p10_ell_torsion_classfunction_tensorization_leyang_group))
                              (f := fun b :
                                  conclusion_leyang_p10_ell_torsion_classfunction_tensorization_leyang_group =>
                                g b) (a := EH))
                    _ = (f a * EG) * EH := by ring
      _ =
          (conclusion_leyang_p10_ell_torsion_classfunction_tensorization_average f * EG) *
            EH := by
            simpa [EG,
              conclusion_leyang_p10_ell_torsion_classfunction_tensorization_average, mul_assoc,
              mul_left_comm, mul_comm] using
              (Finset.expect_mul
                (s := (Finset.univ :
                  Finset conclusion_leyang_p10_ell_torsion_classfunction_tensorization_p10_group))
                (f := fun a :
                    conclusion_leyang_p10_ell_torsion_classfunction_tensorization_p10_group =>
                  f a) (a := EG * EH)).symm
      _ =
          conclusion_leyang_p10_ell_torsion_classfunction_tensorization_average f *
            conclusion_leyang_p10_ell_torsion_classfunction_tensorization_average g *
              conclusion_leyang_p10_ell_torsion_classfunction_tensorization_average h := by
            simp [EG, EH, mul_assoc]
/-- Paper label: `thm:conclusion-leyang-p10-ell-torsion-classfunction-tensorization`. -/
theorem paper_conclusion_leyang_p10_ell_torsion_classfunction_tensorization
    (D : conclusion_leyang_p10_ell_torsion_classfunction_tensorization_data) :
    conclusion_leyang_p10_ell_torsion_classfunction_tensorization_statement D := by
  refine ⟨conclusion_leyang_p10_ell_torsion_classfunction_tensorization_factorized_average, ?_⟩
  intro f g h
  have hTensor :=
    conclusion_leyang_p10_ell_torsion_classfunction_tensorization_factorized_average
      (fun a => f a -
        conclusion_leyang_p10_ell_torsion_classfunction_tensorization_average f)
      (fun b => g b -
        conclusion_leyang_p10_ell_torsion_classfunction_tensorization_average g)
      (fun c => h c -
        conclusion_leyang_p10_ell_torsion_classfunction_tensorization_average h)
  have hf :
      conclusion_leyang_p10_ell_torsion_classfunction_tensorization_average
          (fun a => f a -
            conclusion_leyang_p10_ell_torsion_classfunction_tensorization_average f) =
        0 := by
    simp [conclusion_leyang_p10_ell_torsion_classfunction_tensorization_average,
      Finset.expect_sub_distrib]
  rw [hTensor, hf]
  ring

end

end Omega.Conclusion
