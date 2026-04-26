import Mathlib.Tactic

namespace Omega.POM

/-- Semiring terms over `k` variables for the one-fold normal-form statement. -/
inductive pom_one_fold_normal_form_Term (k : Nat) where
  | pom_one_fold_normal_form_term_const : Nat → pom_one_fold_normal_form_Term k
  | pom_one_fold_normal_form_term_var : Fin k → pom_one_fold_normal_form_Term k
  | pom_one_fold_normal_form_term_add :
      pom_one_fold_normal_form_Term k →
        pom_one_fold_normal_form_Term k → pom_one_fold_normal_form_Term k
  | pom_one_fold_normal_form_term_mul :
      pom_one_fold_normal_form_Term k →
        pom_one_fold_normal_form_Term k → pom_one_fold_normal_form_Term k

/-- Polynomial normal forms over `k` variables, represented by the semiring syntax they generate. -/
inductive pom_one_fold_normal_form_Poly (k : Nat) where
  | pom_one_fold_normal_form_poly_const : Nat → pom_one_fold_normal_form_Poly k
  | pom_one_fold_normal_form_poly_var : Fin k → pom_one_fold_normal_form_Poly k
  | pom_one_fold_normal_form_poly_add :
      pom_one_fold_normal_form_Poly k →
        pom_one_fold_normal_form_Poly k → pom_one_fold_normal_form_Poly k
  | pom_one_fold_normal_form_poly_mul :
      pom_one_fold_normal_form_Poly k →
        pom_one_fold_normal_form_Poly k → pom_one_fold_normal_form_Poly k

/-- Evaluation of one-fold normal-form terms in `Nat`. -/
def pom_one_fold_normal_form_evalTerm {k : Nat} :
    pom_one_fold_normal_form_Term k → (Fin k → Nat) → Nat
  | .pom_one_fold_normal_form_term_const n, _ => n
  | .pom_one_fold_normal_form_term_var i, c => c i
  | .pom_one_fold_normal_form_term_add t u, c =>
      pom_one_fold_normal_form_evalTerm t c + pom_one_fold_normal_form_evalTerm u c
  | .pom_one_fold_normal_form_term_mul t u, c =>
      pom_one_fold_normal_form_evalTerm t c * pom_one_fold_normal_form_evalTerm u c

/-- Evaluation of polynomial normal forms in `Nat`. -/
def pom_one_fold_normal_form_evalPoly {k : Nat} :
    pom_one_fold_normal_form_Poly k → (Fin k → Nat) → Nat
  | .pom_one_fold_normal_form_poly_const n, _ => n
  | .pom_one_fold_normal_form_poly_var i, c => c i
  | .pom_one_fold_normal_form_poly_add P Q, c =>
      pom_one_fold_normal_form_evalPoly P c + pom_one_fold_normal_form_evalPoly Q c
  | .pom_one_fold_normal_form_poly_mul P Q, c =>
      pom_one_fold_normal_form_evalPoly P c * pom_one_fold_normal_form_evalPoly Q c

/-- Paper label: `thm:pom-one-fold-normal-form`. -/
theorem paper_pom_one_fold_normal_form {k : Nat}
    (t : pom_one_fold_normal_form_Term k) :
    ∃ P : pom_one_fold_normal_form_Poly k,
      ∀ c : Fin k → Nat,
        pom_one_fold_normal_form_evalTerm t c =
          pom_one_fold_normal_form_evalPoly P c := by
  induction t with
  | pom_one_fold_normal_form_term_const n =>
      exact ⟨.pom_one_fold_normal_form_poly_const n, by intro c; rfl⟩
  | pom_one_fold_normal_form_term_var i =>
      exact ⟨.pom_one_fold_normal_form_poly_var i, by intro c; rfl⟩
  | pom_one_fold_normal_form_term_add t u ht hu =>
      rcases ht with ⟨P, hP⟩
      rcases hu with ⟨Q, hQ⟩
      refine ⟨.pom_one_fold_normal_form_poly_add P Q, ?_⟩
      intro c
      simp [pom_one_fold_normal_form_evalTerm, pom_one_fold_normal_form_evalPoly, hP c, hQ c]
  | pom_one_fold_normal_form_term_mul t u ht hu =>
      rcases ht with ⟨P, hP⟩
      rcases hu with ⟨Q, hQ⟩
      refine ⟨.pom_one_fold_normal_form_poly_mul P Q, ?_⟩
      intro c
      simp [pom_one_fold_normal_form_evalTerm, pom_one_fold_normal_form_evalPoly, hP c, hQ c]

end Omega.POM
