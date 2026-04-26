import Mathlib.Data.Int.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.EA

/-- Six-variable positive binary ETP terms for the abelian-group audit. -/
inductive stable_audit_abelian_group_classification_term where
  | var : Fin 6 → stable_audit_abelian_group_classification_term
  | op :
      stable_audit_abelian_group_classification_term →
      stable_audit_abelian_group_classification_term →
      stable_audit_abelian_group_classification_term
deriving DecidableEq, Repr

/-- A concrete candidate equation between two ETP terms. -/
structure stable_audit_abelian_group_classification_data where
  lhs : stable_audit_abelian_group_classification_term
  rhs : stable_audit_abelian_group_classification_term

namespace stable_audit_abelian_group_classification_data

open stable_audit_abelian_group_classification_term

/-- Interpretation of `◇` as addition in an additive commutative monoid. -/
def stable_audit_abelian_group_classification_eval {G : Type*} [AddCommMonoid G]
    (ρ : Fin 6 → G) : stable_audit_abelian_group_classification_term → G
  | var i => ρ i
  | op s t =>
      stable_audit_abelian_group_classification_eval ρ s +
        stable_audit_abelian_group_classification_eval ρ t

/-- Variable multiplicities in a positive binary ETP term. -/
def stable_audit_abelian_group_classification_multiplicity :
    stable_audit_abelian_group_classification_term → Fin 6 → ℕ
  | var i, j => if j = i then 1 else 0
  | op s t, j =>
      stable_audit_abelian_group_classification_multiplicity s j +
        stable_audit_abelian_group_classification_multiplicity t j

/-- Multiplicity-weighted sum of a valuation. -/
def stable_audit_abelian_group_classification_weightedSum {G : Type*} [AddCommMonoid G]
    (c : Fin 6 → ℕ) (ρ : Fin 6 → G) : G :=
  ∑ i : Fin 6, c i • ρ i

lemma stable_audit_abelian_group_classification_eval_eq_weightedSum
    {G : Type*} [AddCommMonoid G] (ρ : Fin 6 → G) :
    ∀ t,
      stable_audit_abelian_group_classification_eval ρ t =
        stable_audit_abelian_group_classification_weightedSum
          (stable_audit_abelian_group_classification_multiplicity t) ρ
  | var i => by
      simp [stable_audit_abelian_group_classification_eval,
        stable_audit_abelian_group_classification_multiplicity,
        stable_audit_abelian_group_classification_weightedSum]
  | op s t => by
      rw [stable_audit_abelian_group_classification_eval,
        stable_audit_abelian_group_classification_eval_eq_weightedSum ρ s,
        stable_audit_abelian_group_classification_eval_eq_weightedSum ρ t]
      simp [stable_audit_abelian_group_classification_multiplicity,
        stable_audit_abelian_group_classification_weightedSum, Finset.sum_add_distrib,
        add_nsmul]

lemma stable_audit_abelian_group_classification_weightedSum_int_basis
    (c : Fin 6 → ℕ) (i : Fin 6) :
    stable_audit_abelian_group_classification_weightedSum (G := ℤ) c
        (fun j => if j = i then (1 : ℤ) else 0) = c i := by
  simp [stable_audit_abelian_group_classification_weightedSum]

lemma stable_audit_abelian_group_classification_separate_int
    (D : stable_audit_abelian_group_classification_data)
    (h :
      stable_audit_abelian_group_classification_multiplicity D.lhs ≠
        stable_audit_abelian_group_classification_multiplicity D.rhs) :
    ∃ ρ : Fin 6 → ℤ,
      stable_audit_abelian_group_classification_eval ρ D.lhs ≠
        stable_audit_abelian_group_classification_eval ρ D.rhs := by
  classical
  obtain ⟨i, hi⟩ : ∃ i,
      stable_audit_abelian_group_classification_multiplicity D.lhs i ≠
        stable_audit_abelian_group_classification_multiplicity D.rhs i := by
    by_contra hnone
    apply h
    funext i
    by_contra hi
    exact hnone ⟨i, hi⟩
  refine ⟨fun j => if j = i then (1 : ℤ) else 0, ?_⟩
  intro heq
  rw [stable_audit_abelian_group_classification_eval_eq_weightedSum,
    stable_audit_abelian_group_classification_eval_eq_weightedSum,
    stable_audit_abelian_group_classification_weightedSum_int_basis,
    stable_audit_abelian_group_classification_weightedSum_int_basis] at heq
  exact hi (Int.ofNat.inj heq)

end stable_audit_abelian_group_classification_data

open stable_audit_abelian_group_classification_data

/-- Universal validity in additive commutative groups is exactly equality of variable
multiplicities; unbalanced terms are separated already in `ℤ`. -/
def stable_audit_abelian_group_classification_statement
    (D : stable_audit_abelian_group_classification_data) : Prop :=
  ((∀ (G : Type) [AddCommGroup G], ∀ ρ : Fin 6 → G,
      stable_audit_abelian_group_classification_eval ρ D.lhs =
        stable_audit_abelian_group_classification_eval ρ D.rhs) ↔
      stable_audit_abelian_group_classification_multiplicity D.lhs =
        stable_audit_abelian_group_classification_multiplicity D.rhs) ∧
    (stable_audit_abelian_group_classification_multiplicity D.lhs ≠
        stable_audit_abelian_group_classification_multiplicity D.rhs →
      ∃ ρ : Fin 6 → ℤ,
        stable_audit_abelian_group_classification_eval ρ D.lhs ≠
          stable_audit_abelian_group_classification_eval ρ D.rhs)

/-- thm:stable-audit-abelian-group-classification -/
theorem paper_stable_audit_abelian_group_classification
    (D : stable_audit_abelian_group_classification_data) :
    stable_audit_abelian_group_classification_statement D := by
  constructor
  · constructor
    · intro hvalid
      funext i
      have hbasis :=
        hvalid Int (fun j => if j = i then (1 : Int) else 0)
      rw [stable_audit_abelian_group_classification_eval_eq_weightedSum,
        stable_audit_abelian_group_classification_eval_eq_weightedSum,
        stable_audit_abelian_group_classification_weightedSum_int_basis,
        stable_audit_abelian_group_classification_weightedSum_int_basis] at hbasis
      exact Int.ofNat.inj hbasis
    · intro hmul G _ ρ
      rw [stable_audit_abelian_group_classification_eval_eq_weightedSum,
        stable_audit_abelian_group_classification_eval_eq_weightedSum, hmul]
  · exact D.stable_audit_abelian_group_classification_separate_int

end Omega.EA
