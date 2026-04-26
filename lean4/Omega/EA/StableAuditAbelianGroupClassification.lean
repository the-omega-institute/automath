import Omega.EA.StableAuditAffineCoefficientCriterion

open scoped BigOperators

namespace Omega.EA

open stable_audit_affine_coefficient_criterion_term

/-- Variable multiplicities for a six-variable binary term under the additive interpretation. -/
def stable_audit_abelian_group_classification_multiplicity :
    stable_audit_affine_coefficient_criterion_term → Fin 6 → ℕ
  | var i, j => if j = i then 1 else 0
  | op s t, j =>
      stable_audit_abelian_group_classification_multiplicity s j +
        stable_audit_abelian_group_classification_multiplicity t j

/-- Evaluation of the existing stable-audit terms in an arbitrary abelian group, with
`x ⋄ y = x + y`. -/
def stable_audit_abelian_group_classification_eval
    {G : Type*} [AddCommGroup G] (ρ : Fin 6 → G) :
    stable_audit_affine_coefficient_criterion_term → G
  | var i => ρ i
  | op s t =>
      stable_audit_abelian_group_classification_eval ρ s +
        stable_audit_abelian_group_classification_eval ρ t

/-- The additive linear combination determined by a multiplicity vector. -/
def stable_audit_abelian_group_classification_sum
    {G : Type*} [AddCommGroup G] (m : Fin 6 → ℕ) (ρ : Fin 6 → G) : G :=
  ∑ i : Fin 6, m i • ρ i

lemma stable_audit_abelian_group_classification_eval_eq_sum
    {G : Type*} [AddCommGroup G] (ρ : Fin 6 → G) :
    ∀ t,
      stable_audit_abelian_group_classification_eval ρ t =
        stable_audit_abelian_group_classification_sum
          (stable_audit_abelian_group_classification_multiplicity t) ρ
  | var i => by
      simp [stable_audit_abelian_group_classification_eval,
        stable_audit_abelian_group_classification_sum,
        stable_audit_abelian_group_classification_multiplicity]
  | op s t => by
      rw [stable_audit_abelian_group_classification_eval,
        stable_audit_abelian_group_classification_eval_eq_sum ρ s,
        stable_audit_abelian_group_classification_eval_eq_sum ρ t]
      simp [stable_audit_abelian_group_classification_sum,
        stable_audit_abelian_group_classification_multiplicity, Finset.sum_add_distrib,
        add_nsmul]

lemma stable_audit_abelian_group_classification_sum_basis
    (m : Fin 6 → ℕ) (i : Fin 6) :
    stable_audit_abelian_group_classification_sum
        (G := ℤ) m (fun j => if j = i then (1 : ℤ) else 0) = m i := by
  simp [stable_audit_abelian_group_classification_sum]

/-- Paper-facing statement: two six-variable terms agree in every abelian group under
`x ⋄ y = x + y` iff their variable multiplicity vectors are equal. -/
def stable_audit_abelian_group_classification_statement : Prop :=
  ∀ s t : stable_audit_affine_coefficient_criterion_term,
    (∀ {G : Type} [AddCommGroup G] (ρ : Fin 6 → G),
        stable_audit_abelian_group_classification_eval ρ s =
          stable_audit_abelian_group_classification_eval ρ t) ↔
      stable_audit_abelian_group_classification_multiplicity s =
        stable_audit_abelian_group_classification_multiplicity t

/-- Paper label: `thm:stable-audit-abelian-group-classification`. -/
theorem paper_stable_audit_abelian_group_classification :
    stable_audit_abelian_group_classification_statement := by
  intro s t
  constructor
  · intro h
    funext i
    have hbasis :=
      h (G := ℤ) (fun j => if j = i then (1 : ℤ) else 0)
    rw [stable_audit_abelian_group_classification_eval_eq_sum,
      stable_audit_abelian_group_classification_eval_eq_sum,
      stable_audit_abelian_group_classification_sum_basis,
      stable_audit_abelian_group_classification_sum_basis] at hbasis
    exact Int.ofNat.inj hbasis
  · intro hρ G _ ρ
    rw [stable_audit_abelian_group_classification_eval_eq_sum,
      stable_audit_abelian_group_classification_eval_eq_sum, hρ]

end Omega.EA
