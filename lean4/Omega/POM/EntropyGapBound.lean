import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.POM.KLDefectIdentity

namespace Omega.POM

open scoped BigOperators

section

variable {X : Type*} [Fintype X] [DecidableEq X]

omit [DecidableEq X] in
private lemma pom_entropy_gap_bound_pi_sum_eq_one (d : X → Nat) (pi : X → Real)
    (mu : FiberMicrostate d → Real)
    (hmu_marginal : ∀ x, fiberMarginal d mu x = pi x) (hmu_sum : Finset.univ.sum mu = 1) :
    Finset.univ.sum pi = 1 := by
  calc
    Finset.univ.sum pi = ∑ x : X, fiberMarginal d mu x := by
      refine Finset.sum_congr rfl ?_
      intro x hx
      rw [hmu_marginal x]
    _ = Finset.univ.sum mu := by
      rw [Fintype.sum_sigma]
      refine Finset.sum_congr rfl ?_
      intro x hx
      simp [fiberMarginal]
    _ = 1 := hmu_sum

/-- Paper label: `cor:pom-entropy-gap-bound`. The visible entropy ledger bounds the lift entropy by
the visible entropy plus the weighted logarithmic fiber envelope, and `log dMax` dominates the
weighted term once `d x ≤ dMax` for every visible state. -/
theorem paper_pom_entropy_gap_bound {X : Type*} [Fintype X] [DecidableEq X] (d : X -> Nat)
    (hd : forall x, 0 < d x) (dMax : Nat) (hdMax : forall x, d x <= dMax) (pi : X -> Real)
    (mu : FiberMicrostate d -> Real) (hmu_marginal : forall x, fiberMarginal d mu x = pi x)
    (hmu_nonneg : forall a, 0 <= mu a) (hpi_nonneg : forall x, 0 <= pi x)
    (hmu_sum : Finset.univ.sum mu = 1)
    (hkl_nonneg : 0 <= klDiv mu (fiberUniformLift d pi))
    (hkl_zero_iff : klDiv mu (fiberUniformLift d pi) = 0 <-> mu = fiberUniformLift d pi) :
    liftEntropy d mu - (Finset.univ.sum fun x : X => Real.negMulLog (pi x)) <= Real.log dMax := by
  by_cases hne : (Finset.univ : Finset X).Nonempty
  · obtain ⟨x0, hx0⟩ := hne
    have hdMax_pos_nat : 0 < dMax := lt_of_lt_of_le (hd x0) (hdMax x0)
    have hdMax_pos : 0 < (dMax : Real) := by
      exact_mod_cast hdMax_pos_nat
    have hledger :=
      (paper_pom_kl_ledger_bound d hd pi mu hmu_marginal hmu_nonneg hpi_nonneg hmu_sum
        hkl_nonneg hkl_zero_iff).1
    have hpi_sum : Finset.univ.sum pi = 1 :=
      pom_entropy_gap_bound_pi_sum_eq_one d pi mu hmu_marginal hmu_sum
    have hcapacity_pointwise :
        ∀ x : X, pi x * Real.log (d x) ≤ pi x * Real.log dMax := by
      intro x
      have hd_pos : 0 < (d x : Real) := by
        exact_mod_cast hd x
      have hd_le : (d x : Real) ≤ dMax := by
        exact_mod_cast hdMax x
      have hlog_le : Real.log (d x) ≤ Real.log dMax :=
        Real.log_le_log hd_pos hd_le
      exact mul_le_mul_of_nonneg_left hlog_le (hpi_nonneg x)
    have hcapacity :
        (∑ x : X, pi x * Real.log (d x)) ≤ Real.log dMax := by
      calc
        (∑ x : X, pi x * Real.log (d x)) ≤ ∑ x : X, pi x * Real.log dMax := by
          exact Finset.sum_le_sum fun x hx => hcapacity_pointwise x
        _ = (∑ x : X, pi x) * Real.log dMax := by
          rw [← Finset.sum_mul]
        _ = Real.log dMax := by
          rw [hpi_sum]
          ring
    have hgap :
        liftEntropy d mu - (Finset.univ.sum fun x : X => Real.negMulLog (pi x)) ≤
          ∑ x : X, pi x * Real.log (d x) := by
      linarith
    exact hgap.trans hcapacity
  · have huniv_eq_empty : (Finset.univ : Finset X) = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hne
    have hFiberEmpty : IsEmpty (FiberMicrostate d) := by
      refine ⟨?_⟩
      intro a
      have hx : a.1 ∈ (Finset.univ : Finset X) := Finset.mem_univ _
      rw [huniv_eq_empty] at hx
      simp at hx
    have hsum_zero : Finset.univ.sum mu = 0 := by
      simp
    linarith

end

end Omega.POM
