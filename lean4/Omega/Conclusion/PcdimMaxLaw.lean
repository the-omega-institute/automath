import Mathlib.Data.Finset.Max
import Mathlib.Tactic

namespace Omega.Conclusion

/-- The chapter-local `p`-primary profile of a product is the pointwise sum of the two profiles. -/
def conclusion_pcdim_max_law_product_profile (K L : ℕ → ℕ) : ℕ → ℕ :=
  fun p => K p + L p

/-- The profinite `pcdim` surrogate is the primewise supremum over a finite support set. -/
def conclusion_pcdim_max_law_pcdim (P : Finset ℕ) (d : ℕ → ℕ) : ℕ :=
  P.sup d

/-- On disjoint prime support, at each prime at most one profile contributes. -/
def conclusion_pcdim_max_law_disjoint_support_on
    (P : Finset ℕ) (K L : ℕ → ℕ) : Prop :=
  ∀ p ∈ P, K p = 0 ∨ L p = 0

/-- Concrete finite-support formulation of the paper's primewise max law. -/
def conclusion_pcdim_max_law_statement : Prop :=
  ∀ (P : Finset ℕ) (K L : ℕ → ℕ),
    let dpProd := conclusion_pcdim_max_law_product_profile K L
    (∀ p, dpProd p = K p + L p) ∧
      conclusion_pcdim_max_law_pcdim P dpProd = P.sup (fun p => K p + L p) ∧
      (conclusion_pcdim_max_law_disjoint_support_on P K L →
        conclusion_pcdim_max_law_pcdim P dpProd =
          max (conclusion_pcdim_max_law_pcdim P K) (conclusion_pcdim_max_law_pcdim P L))

lemma conclusion_pcdim_max_law_sup_sum_eq_max_sup
    (P : Finset ℕ) (K L : ℕ → ℕ) :
    conclusion_pcdim_max_law_disjoint_support_on P K L →
      conclusion_pcdim_max_law_pcdim P (conclusion_pcdim_max_law_product_profile K L) =
        max (conclusion_pcdim_max_law_pcdim P K) (conclusion_pcdim_max_law_pcdim P L) := by
  intro hdisj
  induction P using Finset.induction_on with
  | empty =>
      simp [conclusion_pcdim_max_law_pcdim]
  | @insert a s ha ih =>
      have ha0 : K a = 0 ∨ L a = 0 := hdisj a (by simp)
      have hs :
          conclusion_pcdim_max_law_disjoint_support_on s K L := by
        intro p hp
        exact hdisj p (by simp [hp])
      cases ha0 with
      | inl hKa =>
          have hstep := congrArg (fun t => max t (L a)) (ih hs)
          simpa [conclusion_pcdim_max_law_pcdim, conclusion_pcdim_max_law_product_profile, hKa,
            max_assoc, max_left_comm, max_comm] using hstep
      | inr hLa =>
          have hstep := congrArg (fun t => max t (K a)) (ih hs)
          simpa [conclusion_pcdim_max_law_pcdim, conclusion_pcdim_max_law_product_profile, hLa,
            max_assoc, max_left_comm, max_comm] using hstep

/-- Paper label: `prop:conclusion-pcdim-max-law`. -/
theorem paper_conclusion_pcdim_max_law : conclusion_pcdim_max_law_statement := by
  intro P K L
  dsimp
  refine ⟨?_, rfl, ?_⟩
  · intro p
    rfl
  · intro hdisj
    exact conclusion_pcdim_max_law_sup_sum_eq_max_sup P K L hdisj

end Omega.Conclusion
