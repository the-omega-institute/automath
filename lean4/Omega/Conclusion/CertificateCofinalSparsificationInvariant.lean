import Mathlib.Tactic
import Omega.CircleDimension.CertificateInverseLimitAddressing
import Omega.CircleDimension.DyadicCofinalSparsification

namespace Omega.Conclusion

open Omega.CircleDimension

/-- The interval carried by a depth certificate. -/
def conclusion_certificate_cofinal_sparsification_invariant_interval {Cert : Type*}
    (left right : Cert → ℝ) (C : Cert) : Set ℝ :=
  Set.Icc (left C) (right C)

/-- The full inverse-limit intersection of a certificate chain. -/
def conclusion_certificate_cofinal_sparsification_invariant_fullIntersection {Cert : Type*}
    (left right : Cert → ℝ) (chain : ℕ → Cert) : Set ℝ :=
  {θ : ℝ | ∀ n,
    θ ∈ conclusion_certificate_cofinal_sparsification_invariant_interval left right (chain n)}

/-- The inverse-limit intersection after restricting to a cofinal depth subsequence. -/
def conclusion_certificate_cofinal_sparsification_invariant_restrictedIntersection
    {Cert : Type*} (left right : Cert → ℝ) (chain : ℕ → Cert) (depth : ℕ → ℕ) :
    Set ℝ :=
  {θ : ℝ | ∀ j,
    θ ∈
      conclusion_certificate_cofinal_sparsification_invariant_interval left right
        (chain (depth j))}

/-- Iterating one-step nesting gives inclusion from any deeper level to any shallower level. -/
lemma conclusion_certificate_cofinal_sparsification_invariant_nested_subset {Cert : Type*}
    (left right : Cert → ℝ) (chain : ℕ → Cert)
    (hnested :
      ∀ n,
        conclusion_certificate_cofinal_sparsification_invariant_interval left right
            (chain (n + 1)) ⊆
          conclusion_certificate_cofinal_sparsification_invariant_interval left right
            (chain n))
    {n m : ℕ} (hnm : n ≤ m) :
    conclusion_certificate_cofinal_sparsification_invariant_interval left right (chain m) ⊆
      conclusion_certificate_cofinal_sparsification_invariant_interval left right (chain n) := by
  induction hnm with
  | refl =>
      exact Set.Subset.rfl
  | @step m _ ih =>
      exact Set.Subset.trans (hnested m) ih

/-- Concrete statement: every monotone cofinal restriction has the same singleton intersection
and the same merge/equivalence-class certificate as the full nested chain. -/
def conclusion_certificate_cofinal_sparsification_invariant_statement : Prop :=
  ∀ {Cert : Type*} (pointsTo : Cert → ℝ → Prop) (equiv : Cert → Cert → Prop)
    (left right : Cert → ℝ) (chain : ℕ → Cert) (depth : ℕ → ℕ),
    (∀ n,
      conclusion_certificate_cofinal_sparsification_invariant_interval left right
          (chain (n + 1)) ⊆
        conclusion_certificate_cofinal_sparsification_invariant_interval left right
          (chain n)) →
    (∀ ε > 0, ∃ N, ∀ n ≥ N, right (chain n) - left (chain n) < ε) →
    (∀ n, left (chain n) ≤ right (chain n)) →
    (∀ C C' θ, pointsTo C θ → pointsTo C' θ → equiv C C') →
    Monotone depth →
    (∀ n, ∃ j, n ≤ depth j) →
      ∃! θ : ℝ,
        conclusion_certificate_cofinal_sparsification_invariant_fullIntersection
            left right chain = {θ} ∧
          conclusion_certificate_cofinal_sparsification_invariant_restrictedIntersection
              left right chain depth = {θ} ∧
          (∀ C C', pointsTo C θ → pointsTo C' θ → equiv C C')

/-- Paper label: `thm:conclusion-certificate-cofinal-sparsification-invariant`. -/
theorem paper_conclusion_certificate_cofinal_sparsification_invariant :
    conclusion_certificate_cofinal_sparsification_invariant_statement := by
  intro Cert pointsTo equiv left right chain depth hnested hdiam hclosed hmerge hmono hcofinal
  have hfull :
      ∃! θ : ℝ,
        (∀ n, θ ∈ Set.Icc (left (chain n)) (right (chain n))) ∧
          ∀ C C', pointsTo C θ → pointsTo C' θ → equiv C C' :=
    paper_cdim_certificate_inverse_limit_addressing pointsTo equiv left right chain
      (by
        intro n
        exact hnested n)
      hdiam hclosed hmerge
  have hrestricted_unique :
      ∃! θ : ℝ,
        ∀ j, θ ∈ Set.Icc (left (chain (depth j))) (right (chain (depth j))) := by
    refine paper_cdim_dyadic_cofinal_sparsification left right (fun j => chain (depth j)) ?_ ?_ ?_
    · intro j
      exact
        conclusion_certificate_cofinal_sparsification_invariant_nested_subset left right chain
          hnested (hmono (Nat.le_succ j))
    · intro ε hε
      obtain ⟨N, hN⟩ := hdiam ε hε
      obtain ⟨J, hJ⟩ := hcofinal N
      refine ⟨J, ?_⟩
      intro j hj
      exact hN (depth j) (le_trans hJ (hmono hj))
    · intro j
      exact hclosed (depth j)
  rcases hfull with ⟨θ, hθ, hθuniq⟩
  refine ⟨θ, ?_, ?_⟩
  · refine ⟨?_, ?_, hθ.2⟩
    · ext η
      constructor
      · intro hη
        have hη_full : (∀ n, η ∈ Set.Icc (left (chain n)) (right (chain n))) := hη
        exact hθuniq η ⟨hη_full, fun C C' hC hC' => hmerge C C' η hC hC'⟩
      · intro hη
        rw [Set.mem_singleton_iff] at hη
        subst η
        exact hθ.1
    · ext η
      constructor
      · intro hη
        have hη_full : ∀ n, η ∈ Set.Icc (left (chain n)) (right (chain n)) := by
          intro n
          obtain ⟨j, hj⟩ := hcofinal n
          exact
            conclusion_certificate_cofinal_sparsification_invariant_nested_subset left right
              chain hnested hj (hη j)
        have hη_eq : η = θ :=
          hθuniq η ⟨hη_full, fun C C' hC hC' => hmerge C C' η hC hC'⟩
        rw [hη_eq]
        exact Set.mem_singleton θ
      · intro hη
        rw [Set.mem_singleton_iff] at hη
        subst η
        have hθ_mem : ∀ j, θ ∈ Set.Icc (left (chain (depth j))) (right (chain (depth j))) :=
          fun j => hθ.1 (depth j)
        exact hθ_mem
  · intro η hη
    have hη_full :
        (∀ n, η ∈ Set.Icc (left (chain n)) (right (chain n))) := by
      have hη_mem :
          η ∈
            conclusion_certificate_cofinal_sparsification_invariant_fullIntersection
              left right chain := by
        rw [hη.1]
        exact Set.mem_singleton η
      exact hη_mem
    exact hθuniq η ⟨hη_full, hη.2.2⟩

end Omega.Conclusion
