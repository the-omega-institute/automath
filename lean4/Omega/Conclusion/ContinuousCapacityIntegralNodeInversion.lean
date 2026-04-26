import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Omega.Conclusion.BudgetCurveExactTailDifferenceReconstruction
import Omega.Conclusion.CapacityFiniteCompleteness
import Omega.Conclusion.CapacityRamanujanPlateauLaw

namespace Omega.Conclusion

open Finset
open scoped BigOperators

section

variable {X : Type*} [Fintype X] [DecidableEq X]

private theorem conclusion_continuous_capacity_integral_node_inversion_card_eq_tail_sub_tail_succ
    (d : X → ℕ) (k : ℕ) :
    (Finset.univ.filter (fun x => d x = k)).card =
      (Finset.univ.filter fun x => k ≤ d x).card -
        (Finset.univ.filter fun x => k + 1 ≤ d x).card := by
  let A : Finset X := Finset.univ.filter fun x => k ≤ d x
  let B : Finset X := Finset.univ.filter fun x => k + 1 ≤ d x
  have hBA : B ⊆ A := by
    intro x hx
    simp [A, B] at hx ⊢
    omega
  have hsplit : A \ B = Finset.univ.filter (fun x => d x = k) := by
    ext x
    simp [A, B]
    omega
  have hcard :
      (Finset.univ.filter (fun x => d x = k)).card = A.card - B.card := by
    rw [← hsplit, Finset.card_sdiff_of_subset hBA]
  simpa [A, B] using hcard

omit [DecidableEq X] in
private theorem conclusion_continuous_capacity_integral_node_inversion_capacity_mono
    (d : X → ℕ) :
    Monotone (Omega.Conclusion.CapacityRamanujanPlateauLaw.capacityCurve d) := by
  intro s t hst
  unfold Omega.Conclusion.CapacityRamanujanPlateauLaw.capacityCurve
  exact Finset.sum_le_sum fun x hx => min_le_min_left (d x) hst

omit [DecidableEq X] in
private theorem conclusion_continuous_capacity_integral_node_inversion_tailCount_antitone
    (d : X → ℕ) :
    Antitone fun t => Fintype.card {x : X // t ≤ d x} := by
  intro s t hst
  classical
  change Fintype.card {x : X // t ≤ d x} ≤ Fintype.card {x : X // s ≤ d x}
  rw [Fintype.card_of_subtype (Finset.univ.filter fun x => t ≤ d x) (by
    intro x
    simp)]
  rw [Fintype.card_of_subtype (Finset.univ.filter fun x => s ≤ d x) (by
    intro x
    simp)]
  exact Finset.card_le_card fun x hx => by
    simp at hx ⊢
    exact le_trans hst hx

end

/-- Concrete finite data for integer-node inversion of the continuous capacity samples attached to
a multiplicity function. -/
structure conclusion_continuous_capacity_integral_node_inversion_data where
  α : Type*
  instFintype : Fintype α
  instDecidableEq : DecidableEq α
  d : α → ℕ

attribute [instance]
  conclusion_continuous_capacity_integral_node_inversion_data.instFintype
  conclusion_continuous_capacity_integral_node_inversion_data.instDecidableEq

namespace conclusion_continuous_capacity_integral_node_inversion_data

/-- Integer-node samples of the continuous capacity curve. -/
def conclusion_continuous_capacity_integral_node_inversion_continuousCapacity
    (D : conclusion_continuous_capacity_integral_node_inversion_data) (t : ℕ) : ℕ :=
  Omega.Conclusion.CapacityRamanujanPlateauLaw.capacityCurve D.d t

/-- Integer tail counts `N^{≥}(t)`. -/
def conclusion_continuous_capacity_integral_node_inversion_tailCount
    (D : conclusion_continuous_capacity_integral_node_inversion_data) (t : ℕ) : ℕ :=
  Fintype.card {x : D.α // t ≤ D.d x}

/-- Exact multiplicity histogram `n(t)`. -/
def conclusion_continuous_capacity_integral_node_inversion_histogram
    (D : conclusion_continuous_capacity_integral_node_inversion_data) (t : ℕ) : ℕ :=
  Fintype.card {x : D.α // D.d x = t}

/-- Power sums recovered from the multiplicity profile. -/
def conclusion_continuous_capacity_integral_node_inversion_powerSum
    (D : conclusion_continuous_capacity_integral_node_inversion_data) (a : ℕ) : ℕ :=
  Finset.sum (Finset.univ : Finset D.α) fun x => D.d x ^ a

/-- Paper-facing inversion package at integer nodes. -/
def statement (D : conclusion_continuous_capacity_integral_node_inversion_data) : Prop :=
  (∀ t : ℕ,
    1 ≤ t →
      D.conclusion_continuous_capacity_integral_node_inversion_tailCount t =
        D.conclusion_continuous_capacity_integral_node_inversion_continuousCapacity t -
          D.conclusion_continuous_capacity_integral_node_inversion_continuousCapacity (t - 1)) ∧
    (∀ t : ℕ,
      1 ≤ t →
        (D.conclusion_continuous_capacity_integral_node_inversion_histogram t : ℤ) =
          2 * (D.conclusion_continuous_capacity_integral_node_inversion_continuousCapacity t : ℤ) -
            (D.conclusion_continuous_capacity_integral_node_inversion_continuousCapacity (t - 1) :
              ℤ) -
              (D.conclusion_continuous_capacity_integral_node_inversion_continuousCapacity (t + 1) :
                ℤ)) ∧
    ∀ a : ℕ,
      ∃ M : ℕ,
        D.conclusion_continuous_capacity_integral_node_inversion_powerSum a =
          Finset.sum (Finset.range (M + 1))
            (fun t =>
              D.conclusion_continuous_capacity_integral_node_inversion_histogram t * t ^ a)

end conclusion_continuous_capacity_integral_node_inversion_data

open conclusion_continuous_capacity_integral_node_inversion_data

/-- Paper label: `thm:conclusion-continuous-capacity-integral-node-inversion`. At integer nodes,
the first discrete difference of the continuous capacity samples is the tail-count function, a
second difference recovers the exact multiplicity histogram, and therefore every power sum factors
through that histogram. -/
theorem paper_conclusion_continuous_capacity_integral_node_inversion
    (D : conclusion_continuous_capacity_integral_node_inversion_data) : D.statement := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    simpa [conclusion_continuous_capacity_integral_node_inversion_continuousCapacity,
      conclusion_continuous_capacity_integral_node_inversion_tailCount,
      Omega.Conclusion.CapacityRamanujanPlateauLaw.deltaCapacity] using
      (Omega.Conclusion.CapacityRamanujanPlateauLaw.deltaCapacity_eq_card_ge D.d t ht).symm
  · intro t ht
    have htail_t :
        D.conclusion_continuous_capacity_integral_node_inversion_tailCount t =
          D.conclusion_continuous_capacity_integral_node_inversion_continuousCapacity t -
            D.conclusion_continuous_capacity_integral_node_inversion_continuousCapacity (t - 1) :=
      by
        simpa [conclusion_continuous_capacity_integral_node_inversion_continuousCapacity,
          conclusion_continuous_capacity_integral_node_inversion_tailCount,
          Omega.Conclusion.CapacityRamanujanPlateauLaw.deltaCapacity] using
          (Omega.Conclusion.CapacityRamanujanPlateauLaw.deltaCapacity_eq_card_ge D.d t ht).symm
    have htail_succ :
        D.conclusion_continuous_capacity_integral_node_inversion_tailCount (t + 1) =
          D.conclusion_continuous_capacity_integral_node_inversion_continuousCapacity (t + 1) -
            D.conclusion_continuous_capacity_integral_node_inversion_continuousCapacity t := by
      simpa [conclusion_continuous_capacity_integral_node_inversion_continuousCapacity,
        conclusion_continuous_capacity_integral_node_inversion_tailCount,
        Omega.Conclusion.CapacityRamanujanPlateauLaw.deltaCapacity] using
        (Omega.Conclusion.CapacityRamanujanPlateauLaw.deltaCapacity_eq_card_ge D.d (t + 1)
          (Nat.succ_le_succ (Nat.zero_le t))).symm
    have hhist_nat :
        D.conclusion_continuous_capacity_integral_node_inversion_histogram t =
          D.conclusion_continuous_capacity_integral_node_inversion_tailCount t -
            D.conclusion_continuous_capacity_integral_node_inversion_tailCount (t + 1) := by
      unfold conclusion_continuous_capacity_integral_node_inversion_histogram
        conclusion_continuous_capacity_integral_node_inversion_tailCount
      rw [Fintype.card_of_subtype (Finset.univ.filter fun x => D.d x = t) (by
        intro x
        simp)]
      rw [Fintype.card_of_subtype (Finset.univ.filter fun x => t ≤ D.d x) (by
        intro x
        simp)]
      rw [Fintype.card_of_subtype (Finset.univ.filter fun x => t + 1 ≤ D.d x) (by
        intro x
        simp)]
      exact
        conclusion_continuous_capacity_integral_node_inversion_card_eq_tail_sub_tail_succ D.d t
    have htail_le :
        D.conclusion_continuous_capacity_integral_node_inversion_tailCount (t + 1) ≤
          D.conclusion_continuous_capacity_integral_node_inversion_tailCount t := by
      exact
        conclusion_continuous_capacity_integral_node_inversion_tailCount_antitone D.d
          (Nat.le_succ t)
    have hcap_prev_le :
        D.conclusion_continuous_capacity_integral_node_inversion_continuousCapacity (t - 1) ≤
          D.conclusion_continuous_capacity_integral_node_inversion_continuousCapacity t := by
      exact
        conclusion_continuous_capacity_integral_node_inversion_capacity_mono D.d (Nat.sub_le _ _)
    have hcap_le_succ :
        D.conclusion_continuous_capacity_integral_node_inversion_continuousCapacity t ≤
          D.conclusion_continuous_capacity_integral_node_inversion_continuousCapacity (t + 1) := by
      exact conclusion_continuous_capacity_integral_node_inversion_capacity_mono D.d (Nat.le_succ t)
    have hhist_int :
        (D.conclusion_continuous_capacity_integral_node_inversion_histogram t : ℤ) =
          (D.conclusion_continuous_capacity_integral_node_inversion_tailCount t : ℤ) -
            D.conclusion_continuous_capacity_integral_node_inversion_tailCount (t + 1) := by
      rw [hhist_nat]
      exact Int.ofNat_sub htail_le
    calc
      (D.conclusion_continuous_capacity_integral_node_inversion_histogram t : ℤ) =
          ((D.conclusion_continuous_capacity_integral_node_inversion_tailCount t : ℤ) -
            D.conclusion_continuous_capacity_integral_node_inversion_tailCount (t + 1)) := hhist_int
      _ =
          ((D.conclusion_continuous_capacity_integral_node_inversion_continuousCapacity t -
                D.conclusion_continuous_capacity_integral_node_inversion_continuousCapacity
                  (t - 1) : ℕ) : ℤ) -
            (D.conclusion_continuous_capacity_integral_node_inversion_continuousCapacity (t + 1) -
                D.conclusion_continuous_capacity_integral_node_inversion_continuousCapacity t : ℕ) :=
        by rw [htail_t, htail_succ]
      _ =
          ((D.conclusion_continuous_capacity_integral_node_inversion_continuousCapacity t : ℤ) -
              D.conclusion_continuous_capacity_integral_node_inversion_continuousCapacity (t - 1)) -
            ((D.conclusion_continuous_capacity_integral_node_inversion_continuousCapacity (t + 1) :
                ℤ) -
              D.conclusion_continuous_capacity_integral_node_inversion_continuousCapacity t) := by
                rw [Int.ofNat_sub hcap_prev_le, Int.ofNat_sub hcap_le_succ]
      _ =
          2 * (D.conclusion_continuous_capacity_integral_node_inversion_continuousCapacity t : ℤ) -
            (D.conclusion_continuous_capacity_integral_node_inversion_continuousCapacity (t - 1) :
              ℤ) -
              (D.conclusion_continuous_capacity_integral_node_inversion_continuousCapacity (t + 1) :
                ℤ) := by ring
  · intro a
    have hcomplete :
        let h : ℕ → ℕ := fun k => Fintype.card {x : D.α // D.d x = k}
        let N : ℕ → ℕ := fun t => Fintype.card {x : D.α // t ≤ D.d x}
        let C : ℕ → ℕ := fun t => Omega.Conclusion.CapacityRamanujanPlateauLaw.capacityCurve D.d t
        Omega.Conclusion.FiniteMultiplicityDataEquivalent (X := D.α) h N C
          (fun q => Finset.sum (Finset.univ : Finset D.α) (fun x => D.d x ^ q)) := by
      simpa using paper_conclusion_capacity_finite_completeness_internal (X := D.α) D.d
    dsimp [Omega.Conclusion.FiniteMultiplicityDataEquivalent] at hcomplete
    rcases hcomplete with ⟨M, hsupport, htail, hhist, hmoment⟩
    refine ⟨M, ?_⟩
    simpa [conclusion_continuous_capacity_integral_node_inversion_powerSum,
      conclusion_continuous_capacity_integral_node_inversion_histogram] using hmoment a

end Omega.Conclusion
