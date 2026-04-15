import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Omega.Conclusion.SectionLedgerKL

namespace Omega.Conclusion.SectionLedgerCapacityFunctional

open Real Finset intervalIntegral
open Omega.Conclusion.SectionLedgerKL

variable {X : Type*} [Fintype X] [Nonempty X]

/-- Continuous capacity curve `C^cont(T) = Σ_x min(d(x), T)`.
    prop:conclusion-section-ledger-capacity-functional -/
noncomputable def capacityCurve (d : X → ℕ) (T : ℝ) : ℝ :=
  ∑ x, min (d x : ℝ) T

/-- Fiberwise capacity functional obtained by integrating `1 / T` up to the fiber size.
    For each fiber this contributes `log d(x) + 1`, matching the paper's integration-by-parts
    normalization. `prop:conclusion-section-ledger-capacity-functional` -/
noncomputable def capacityFunctional (d : X → ℕ) : ℝ :=
  ∑ x, ((∫ t : ℝ in (1 : ℝ)..(d x : ℝ), 1 / t) + 1)

omit [Nonempty X] in
/-- At scale `T = 1`, every positive fiber contributes exactly `1`.
    prop:conclusion-section-ledger-capacity-functional -/
theorem capacityCurve_one (d : X → ℕ) (hd : ∀ x, 0 < d x) :
    capacityCurve d 1 = (Fintype.card X : ℝ) := by
  unfold capacityCurve
  have hsum : ∑ x : X, min (d x : ℝ) (1 : ℝ) = ∑ x : X, (1 : ℝ) := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    have hx' : (1 : ℝ) ≤ (d x : ℝ) := by exact_mod_cast hd x
    rw [min_eq_right hx']
  rw [hsum]
  simp

omit [Nonempty X] in
/-- The integrated capacity functional is the section-ledger log sum plus the `T = 1` boundary
    term `|X|`.
    prop:conclusion-section-ledger-capacity-functional -/
theorem capacityFunctional_eq_log_sum_add_card (d : X → ℕ) (hd : ∀ x, 0 < d x) :
    capacityFunctional d = (∑ x, Real.log (d x : ℝ)) + (Fintype.card X : ℝ) := by
  unfold capacityFunctional
  rw [Finset.sum_add_distrib]
  congr 1
  · refine Finset.sum_congr rfl ?_
    intro x hx
    have hd_pos : (0 : ℝ) < (d x : ℝ) := by exact_mod_cast hd x
    simpa using integral_one_div_of_pos (show (0 : ℝ) < 1 by norm_num) hd_pos
  · simp

/-- Paper package: the capacity functional reproduces the section-ledger log sum after subtracting
    the `T = 1` boundary term, and the same log sum is identified by the KL ledger identity.
    prop:conclusion-section-ledger-capacity-functional -/
theorem paper_conclusion_section_ledger_capacity_functional (d : X → ℕ) (N : ℕ)
    (hN : 0 < N) (hd : ∀ x, 0 < d x) :
    (∑ x, Real.log (d x : ℝ)) = -(Fintype.card X : ℝ) + capacityFunctional d ∧
      capacityCurve d 1 = (Fintype.card X : ℝ) ∧
      (1 / (Fintype.card X : ℝ)) * (∑ x, Real.log (d x : ℝ)) =
        Real.log ((N : ℝ) / (Fintype.card X : ℝ)) -
          klDivergence uniform (pushforward d N) := by
  have hcap := capacityFunctional_eq_log_sum_add_card d hd
  have hone := capacityCurve_one d hd
  have hkl := section_ledger_kl_identity d N hN hd
  refine ⟨?_, hone, hkl⟩
  linarith

end Omega.Conclusion.SectionLedgerCapacityFunctional
