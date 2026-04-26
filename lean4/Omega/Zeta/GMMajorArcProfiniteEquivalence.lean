import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.Zeta.GmFibonacciSubtowerEntrypointCriterion

namespace Omega.Zeta

noncomputable section

open scoped BigOperators

/-- The major-arc side of the comparison: the rational-frequency sum is bounded by the Pisano
period proxy. -/
def gm_major_arc_profinite_equivalence_period (q : ℕ) : ℕ :=
  gmFibonacciEntrypoint q

/-- Rational-frequency sum over one Pisano-style period proxy. -/
def gm_major_arc_profinite_equivalence_frequency_sum (c : ℝ) (q : ℕ) : ℝ :=
  Finset.sum (Finset.range (gm_major_arc_profinite_equivalence_period q)) (fun j => c ^ j)

/-- Period-normalized rational-frequency sum. -/
def gm_major_arc_profinite_equivalence_normalized_frequency_sum (c : ℝ) (q : ℕ) : ℝ :=
  gm_major_arc_profinite_equivalence_frequency_sum c q / gm_major_arc_profinite_equivalence_period q

/-- The major-arc side of the comparison: the rational-frequency sum is bounded by the Pisano
period proxy. -/
def gm_major_arc_profinite_equivalence_major_arc (c : ℝ) (q : ℕ) : Prop :=
  gm_major_arc_profinite_equivalence_frequency_sum c q ≤ gm_major_arc_profinite_equivalence_period q

/-- The profinite side of the comparison: after dividing by the Pisano period proxy, the same
character sum is bounded by `1`. -/
def gm_major_arc_profinite_equivalence_profinite (c : ℝ) (q : ℕ) : Prop :=
  gm_major_arc_profinite_equivalence_normalized_frequency_sum c q ≤ 1

/-- Paper-facing universal statement for the major-arc/profinite comparison. -/
def gm_major_arc_profinite_equivalence_statement : Prop :=
  ∀ (q : ℕ) {c : ℝ}, 0 < q → 0 ≤ c → c < 1 →
    Nonempty (FibProfiniteCompletion ≃+* Zhat) ∧
      0 < gm_major_arc_profinite_equivalence_period q ∧
      (gm_major_arc_profinite_equivalence_major_arc c q ↔
        gm_major_arc_profinite_equivalence_profinite c q) ∧
      gm_major_arc_profinite_equivalence_major_arc c q ∧
      gm_major_arc_profinite_equivalence_profinite c q

/-- Paper label: `thm:gm-major-arc-profinite-equivalence`. The existing major-arc criterion gives
the profinite axis and the corresponding major-arc bounds; since the Pisano-style period is
positive, the unnormalized and normalized formulations are equivalent. -/
theorem paper_gm_major_arc_profinite_equivalence :
    gm_major_arc_profinite_equivalence_statement := by
  intro q c hq hc_nonneg hc_lt_one
  have hAxis : Nonempty (FibProfiniteCompletion ≃+* Zhat) := ⟨paper_gm_fibonacci_profinite_axis⟩
  have hPeriodPos : 0 < gm_major_arc_profinite_equivalence_period q := by
    exact gmFibonacciEntrypoint_pos hq
  have hMajorArc :
      gm_major_arc_profinite_equivalence_major_arc c q := by
    unfold gm_major_arc_profinite_equivalence_major_arc
    unfold gm_major_arc_profinite_equivalence_frequency_sum
    unfold gm_major_arc_profinite_equivalence_period
    calc
      Finset.sum (Finset.range (gmFibonacciEntrypoint q)) (fun j => c ^ j) ≤
          Finset.sum (Finset.range (gmFibonacciEntrypoint q)) (fun _j => (1 : ℝ)) := by
            exact Finset.sum_le_sum (fun j _hj => pow_le_one₀ hc_nonneg hc_lt_one.le)
      _ = gmFibonacciEntrypoint q := by simp
  have hPeriodRealPos : 0 < (gm_major_arc_profinite_equivalence_period q : ℝ) := by
    exact_mod_cast hPeriodPos
  have hProfinite :
      gm_major_arc_profinite_equivalence_profinite c q := by
    unfold gm_major_arc_profinite_equivalence_profinite
    unfold gm_major_arc_profinite_equivalence_normalized_frequency_sum
    exact (div_le_iff₀ hPeriodRealPos).2 <| by simpa using hMajorArc
  have hIff :
      gm_major_arc_profinite_equivalence_major_arc c q ↔
        gm_major_arc_profinite_equivalence_profinite c q := by
    unfold gm_major_arc_profinite_equivalence_major_arc
    unfold gm_major_arc_profinite_equivalence_profinite
    unfold gm_major_arc_profinite_equivalence_normalized_frequency_sum
    constructor
    · intro h
      exact (div_le_iff₀ hPeriodRealPos).2 <| by simpa using h
    · intro h
      have h' :
          gm_major_arc_profinite_equivalence_frequency_sum c q ≤
            1 * (gm_major_arc_profinite_equivalence_period q : ℝ) :=
        (div_le_iff₀ hPeriodRealPos).1 h
      simpa [one_mul] using h'
  exact ⟨hAxis, hPeriodPos, hIff, hMajorArc, hProfinite⟩

end

end Omega.Zeta
