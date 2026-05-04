import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- Requested data handle for the finite `S10 × S3 × (S4 × C2)` tensor model. -/
abbrev xi_time_part62d_triple_frobenius_classfunction_tensor_independence_data := PUnit

/-- The `S10` Frobenius factor. -/
abbrev xi_time_part62d_triple_frobenius_classfunction_tensor_independence_s10_group :=
  Equiv.Perm (Fin 10)

/-- The `S3` Lee--Yang Frobenius factor. -/
abbrev xi_time_part62d_triple_frobenius_classfunction_tensor_independence_s3_group :=
  Equiv.Perm (Fin 3)

/-- The `S4 × C2` auxiliary Frobenius factor. -/
abbrev xi_time_part62d_triple_frobenius_classfunction_tensor_independence_s4c2_group :=
  Equiv.Perm (Fin 4) × Equiv.Perm (Fin 2)

/-- The finite product model for the unramified triple Frobenius class. -/
abbrev xi_time_part62d_triple_frobenius_classfunction_tensor_independence_joint_group :=
  xi_time_part62d_triple_frobenius_classfunction_tensor_independence_s10_group ×
    (xi_time_part62d_triple_frobenius_classfunction_tensor_independence_s3_group ×
      xi_time_part62d_triple_frobenius_classfunction_tensor_independence_s4c2_group)

/-- Uniform finite-group average. -/
def xi_time_part62d_triple_frobenius_classfunction_tensor_independence_average
    {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  𝔼 a, f a

/-- Product-average factorization and centered mixed-moment vanishing. -/
def xi_time_part62d_triple_frobenius_classfunction_tensor_independence_statement
    (_D : xi_time_part62d_triple_frobenius_classfunction_tensor_independence_data) : Prop :=
  (∀ f : xi_time_part62d_triple_frobenius_classfunction_tensor_independence_s10_group → ℝ,
      ∀ g : xi_time_part62d_triple_frobenius_classfunction_tensor_independence_s3_group → ℝ,
      ∀ h : xi_time_part62d_triple_frobenius_classfunction_tensor_independence_s4c2_group → ℝ,
        xi_time_part62d_triple_frobenius_classfunction_tensor_independence_average
            (fun x : xi_time_part62d_triple_frobenius_classfunction_tensor_independence_joint_group =>
              f x.1 * g x.2.1 * h x.2.2) =
          xi_time_part62d_triple_frobenius_classfunction_tensor_independence_average f *
            xi_time_part62d_triple_frobenius_classfunction_tensor_independence_average g *
              xi_time_part62d_triple_frobenius_classfunction_tensor_independence_average h) ∧
    ∀ f : xi_time_part62d_triple_frobenius_classfunction_tensor_independence_s10_group → ℝ,
      ∀ g : xi_time_part62d_triple_frobenius_classfunction_tensor_independence_s3_group → ℝ,
      ∀ h : xi_time_part62d_triple_frobenius_classfunction_tensor_independence_s4c2_group → ℝ,
        xi_time_part62d_triple_frobenius_classfunction_tensor_independence_average
            (fun x : xi_time_part62d_triple_frobenius_classfunction_tensor_independence_joint_group =>
              (f x.1 -
                  xi_time_part62d_triple_frobenius_classfunction_tensor_independence_average f) *
                (g x.2.1 -
                  xi_time_part62d_triple_frobenius_classfunction_tensor_independence_average g) *
                  (h x.2.2 -
                    xi_time_part62d_triple_frobenius_classfunction_tensor_independence_average h)) =
          0

/-- Finite-product averaging factors over the three uniform Frobenius coordinates. -/
lemma xi_time_part62d_triple_frobenius_classfunction_tensor_independence_factorized_average
    (f : xi_time_part62d_triple_frobenius_classfunction_tensor_independence_s10_group → ℝ)
    (g : xi_time_part62d_triple_frobenius_classfunction_tensor_independence_s3_group → ℝ)
    (h : xi_time_part62d_triple_frobenius_classfunction_tensor_independence_s4c2_group → ℝ) :
    xi_time_part62d_triple_frobenius_classfunction_tensor_independence_average
        (fun x : xi_time_part62d_triple_frobenius_classfunction_tensor_independence_joint_group =>
          f x.1 * g x.2.1 * h x.2.2) =
      xi_time_part62d_triple_frobenius_classfunction_tensor_independence_average f *
        xi_time_part62d_triple_frobenius_classfunction_tensor_independence_average g *
          xi_time_part62d_triple_frobenius_classfunction_tensor_independence_average h := by
    let EG : ℝ :=
      xi_time_part62d_triple_frobenius_classfunction_tensor_independence_average g
    let EH : ℝ :=
      xi_time_part62d_triple_frobenius_classfunction_tensor_independence_average h
    calc
      xi_time_part62d_triple_frobenius_classfunction_tensor_independence_average
          (fun x : xi_time_part62d_triple_frobenius_classfunction_tensor_independence_joint_group =>
            f x.1 * g x.2.1 * h x.2.2) =
          xi_time_part62d_triple_frobenius_classfunction_tensor_independence_average
            (fun a : xi_time_part62d_triple_frobenius_classfunction_tensor_independence_s10_group =>
              xi_time_part62d_triple_frobenius_classfunction_tensor_independence_average
                (fun yz :
                    xi_time_part62d_triple_frobenius_classfunction_tensor_independence_s3_group ×
                      xi_time_part62d_triple_frobenius_classfunction_tensor_independence_s4c2_group =>
                  f a * g yz.1 * h yz.2)) := by
            simpa [xi_time_part62d_triple_frobenius_classfunction_tensor_independence_average] using
              (Finset.expect_product'
                (s := (Finset.univ :
                  Finset
                    xi_time_part62d_triple_frobenius_classfunction_tensor_independence_s10_group))
                (t := (Finset.univ :
                  Finset
                    (xi_time_part62d_triple_frobenius_classfunction_tensor_independence_s3_group ×
                      xi_time_part62d_triple_frobenius_classfunction_tensor_independence_s4c2_group)))
                (f := fun a yz => f a * g yz.1 * h yz.2))
      _ =
          xi_time_part62d_triple_frobenius_classfunction_tensor_independence_average
            (fun a : xi_time_part62d_triple_frobenius_classfunction_tensor_independence_s10_group =>
              (f a * EG) * EH) := by
            refine Finset.expect_congr rfl ?_
            intro a _ha
            calc
              xi_time_part62d_triple_frobenius_classfunction_tensor_independence_average
                  (fun yz :
                      xi_time_part62d_triple_frobenius_classfunction_tensor_independence_s3_group ×
                        xi_time_part62d_triple_frobenius_classfunction_tensor_independence_s4c2_group =>
                    f a * g yz.1 * h yz.2) =
                xi_time_part62d_triple_frobenius_classfunction_tensor_independence_average
                  (fun b :
                      xi_time_part62d_triple_frobenius_classfunction_tensor_independence_s3_group =>
                    xi_time_part62d_triple_frobenius_classfunction_tensor_independence_average
                      (fun c :
                          xi_time_part62d_triple_frobenius_classfunction_tensor_independence_s4c2_group =>
                        (f a * g b) * h c)) := by
                  simpa [xi_time_part62d_triple_frobenius_classfunction_tensor_independence_average,
                    mul_assoc] using
                    (Finset.expect_product'
                      (s := (Finset.univ :
                        Finset
                          xi_time_part62d_triple_frobenius_classfunction_tensor_independence_s3_group))
                      (t := (Finset.univ :
                        Finset
                          xi_time_part62d_triple_frobenius_classfunction_tensor_independence_s4c2_group))
                      (f := fun b c => (f a * g b) * h c))
              _ =
                xi_time_part62d_triple_frobenius_classfunction_tensor_independence_average
                  (fun b :
                      xi_time_part62d_triple_frobenius_classfunction_tensor_independence_s3_group =>
                    (f a * g b) * EH) := by
                  refine Finset.expect_congr rfl ?_
                  intro b _hb
                  simpa [EH,
                    xi_time_part62d_triple_frobenius_classfunction_tensor_independence_average,
                    mul_assoc, mul_left_comm, mul_comm] using
                    (Finset.expect_mul
                      (s := (Finset.univ :
                        Finset
                          xi_time_part62d_triple_frobenius_classfunction_tensor_independence_s4c2_group))
                      (f := fun c :
                          xi_time_part62d_triple_frobenius_classfunction_tensor_independence_s4c2_group =>
                        h c) (a := f a * g b)).symm
              _ = (f a * EG) * EH := by
                  calc
                    xi_time_part62d_triple_frobenius_classfunction_tensor_independence_average
                        (fun b :
                            xi_time_part62d_triple_frobenius_classfunction_tensor_independence_s3_group =>
                          (f a * g b) * EH) =
                      f a *
                        xi_time_part62d_triple_frobenius_classfunction_tensor_independence_average
                          (fun b :
                              xi_time_part62d_triple_frobenius_classfunction_tensor_independence_s3_group =>
                            g b * EH) := by
                            simpa [
                              xi_time_part62d_triple_frobenius_classfunction_tensor_independence_average,
                              mul_assoc, mul_left_comm, mul_comm] using
                              (Finset.mul_expect
                                (s := (Finset.univ :
                                  Finset
                                    xi_time_part62d_triple_frobenius_classfunction_tensor_independence_s3_group))
                                (f := fun b :
                                    xi_time_part62d_triple_frobenius_classfunction_tensor_independence_s3_group =>
                                  g b * EH) (a := f a)).symm
                    _ = f a * (EG * EH) := by
                          congr 1
                          symm
                          simpa [EG,
                            xi_time_part62d_triple_frobenius_classfunction_tensor_independence_average,
                            mul_assoc, mul_left_comm, mul_comm] using
                            (Finset.expect_mul
                              (s := (Finset.univ :
                                Finset
                                  xi_time_part62d_triple_frobenius_classfunction_tensor_independence_s3_group))
                              (f := fun b :
                                  xi_time_part62d_triple_frobenius_classfunction_tensor_independence_s3_group =>
                                g b) (a := EH))
                    _ = (f a * EG) * EH := by ring
      _ =
          (xi_time_part62d_triple_frobenius_classfunction_tensor_independence_average f * EG) *
            EH := by
            simpa [EG,
              xi_time_part62d_triple_frobenius_classfunction_tensor_independence_average, mul_assoc,
              mul_left_comm, mul_comm] using
              (Finset.expect_mul
                (s := (Finset.univ :
                  Finset
                    xi_time_part62d_triple_frobenius_classfunction_tensor_independence_s10_group))
                (f := fun a :
                    xi_time_part62d_triple_frobenius_classfunction_tensor_independence_s10_group =>
                  f a) (a := EG * EH)).symm
      _ =
          xi_time_part62d_triple_frobenius_classfunction_tensor_independence_average f *
            xi_time_part62d_triple_frobenius_classfunction_tensor_independence_average g *
              xi_time_part62d_triple_frobenius_classfunction_tensor_independence_average h := by
            simp [EG, EH, mul_assoc]
/-- Paper label:
`thm:xi-time-part62d-triple-frobenius-classfunction-tensor-independence`. -/
theorem paper_xi_time_part62d_triple_frobenius_classfunction_tensor_independence
    (D : xi_time_part62d_triple_frobenius_classfunction_tensor_independence_data) :
    xi_time_part62d_triple_frobenius_classfunction_tensor_independence_statement D := by
  refine ⟨xi_time_part62d_triple_frobenius_classfunction_tensor_independence_factorized_average, ?_⟩
  intro f g h
  have hTensor :=
    xi_time_part62d_triple_frobenius_classfunction_tensor_independence_factorized_average
      (fun a => f a -
        xi_time_part62d_triple_frobenius_classfunction_tensor_independence_average f)
      (fun b => g b -
        xi_time_part62d_triple_frobenius_classfunction_tensor_independence_average g)
      (fun c => h c -
        xi_time_part62d_triple_frobenius_classfunction_tensor_independence_average h)
  have hf :
      xi_time_part62d_triple_frobenius_classfunction_tensor_independence_average
          (fun a => f a -
            xi_time_part62d_triple_frobenius_classfunction_tensor_independence_average f) =
        0 := by
    simp [xi_time_part62d_triple_frobenius_classfunction_tensor_independence_average,
      Finset.expect_sub_distrib]
  rw [hTensor, hf]
  ring

end

end Omega.Zeta
