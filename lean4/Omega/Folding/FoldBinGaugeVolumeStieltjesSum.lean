import Mathlib.Tactic
import Omega.Conclusion.CapacityRamanujanPlateauLaw
import Omega.Folding.BinGaugeVolume

open scoped BigOperators

namespace Omega.Folding

open Omega.Conclusion.CapacityRamanujanPlateauLaw

/-- The zero-based tail count: the number of fibers with multiplicity at least `k + 1`. -/
def foldBinTailCount {α : Type*} [Fintype α] (d : α → ℕ) (k : ℕ) : ℕ :=
  Fintype.card {a // k + 1 ≤ d a}

/-- The logarithmic gauge volume written as the finite Stieltjes sum against the tail-count
sequence, truncated at the ambient multiplicity bound `2^m`. -/
def logVolumeTailFormula {α : Type*} [Fintype α] (m : ℕ) (d : α → ℕ) : Prop :=
  binGaugeLogVolume d =
    ∑ k ∈ Finset.range (2 ^ m), (foldBinTailCount d k : ℝ) * Real.log (k + 1)

/-- The same logarithmic gauge volume written using discrete differences of the integer capacity
curve `C(t) = Σ_w min(d(w), t)`. -/
def capacityDifferenceFormula {α : Type*} [Fintype α] (m : ℕ) (d : α → ℕ) : Prop :=
  binGaugeLogVolume d =
    ∑ k ∈ Finset.range (2 ^ m),
      ((capacityCurve d (k + 1) - capacityCurve d k : ℕ) : ℝ) * Real.log (k + 1)

private lemma log_factorial_eq_sum_range (n : ℕ) :
    Real.log ((Nat.factorial n : ℝ)) = ∑ k ∈ Finset.range n, Real.log (k + 1) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hn1_ne : ((n : ℝ) + 1) ≠ 0 := by
        positivity
      have hfac_ne : ((Nat.factorial n : ℕ) : ℝ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero n
      calc
        Real.log ((Nat.factorial (n + 1) : ℝ))
            = Real.log ((((n + 1) * Nat.factorial n : ℕ) : ℕ) : ℝ) := by
                rw [Nat.factorial_succ]
        _ = Real.log ((n + 1 : ℝ) * (Nat.factorial n : ℝ)) := by
              norm_num [Nat.cast_mul]
        _ = Real.log (n + 1) + Real.log ((Nat.factorial n : ℝ)) := by
              exact Real.log_mul hn1_ne hfac_ne
        _ = Real.log (n + 1) + ∑ k ∈ Finset.range n, Real.log (k + 1) := by
              rw [ih]
        _ = ∑ k ∈ Finset.range (n + 1), Real.log (k + 1) := by
              simpa [add_comm] using
                (Finset.sum_range_succ (f := fun k => Real.log (k + 1)) n).symm

private lemma sum_range_eq_sum_range_indicator (n B : ℕ) (hnB : n ≤ B) :
    ∑ k ∈ Finset.range n, Real.log (k + 1) =
      ∑ k ∈ Finset.range B, if k < n then Real.log (k + 1) else 0 := by
  have hfilter : Finset.range n = (Finset.range B).filter (fun k => k < n) := by
    ext k
    simp [Finset.mem_filter, Finset.mem_range]
    omega
  rw [hfilter, Finset.sum_filter]

private lemma sum_indicator_eq_tailCount_mul {α : Type*} [Fintype α] (d : α → ℕ) (k : ℕ) :
    ∑ a, (if k < d a then Real.log (k + 1) else 0) =
      (foldBinTailCount d k : ℝ) * Real.log (k + 1) := by
  classical
  calc
    ∑ a, (if k < d a then Real.log (k + 1) else 0)
        = ∑ a, (if k + 1 ≤ d a then Real.log (k + 1) else 0) := by
            refine Finset.sum_congr rfl ?_
            intro a _
            by_cases h : k + 1 ≤ d a
            · have hklt : k < d a := by omega
              simp [h, hklt]
            · have hknot : ¬ k < d a := by omega
              simp [h, hknot]
    _ = ∑ a ∈ (Finset.univ : Finset α).filter (fun a => k + 1 ≤ d a), Real.log (k + 1) := by
          rw [Finset.sum_filter]
    _ = (((Finset.univ : Finset α).filter (fun a => k + 1 ≤ d a)).card : ℝ) * Real.log (k + 1) := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ = (foldBinTailCount d k : ℝ) * Real.log (k + 1) := by
          have hcard :
              Fintype.card {a // k + 1 ≤ d a} =
                ((Finset.univ : Finset α).filter (fun a => k + 1 ≤ d a)).card := by
            simpa using
              (Fintype.card_of_subtype (p := fun a : α => k + 1 ≤ d a)
                ((Finset.univ : Finset α).filter fun a => k + 1 ≤ d a) (by
                  intro x
                  simp))
          rw [foldBinTailCount, hcard]

/-- Paper label: `prop:fold-bin-gauge-volume-stieltjes-sum`. Expanding each `log(d(w)!)` into the
finite sum `Σ_{k < d(w)} log(k + 1)` gives the exact tail-count Stieltjes formula, and the
capacity-curve difference identity is the integer jump formula for `t ↦ Σ_w min(d(w), t)`. -/
theorem paper_fold_bin_gauge_volume_stieltjes_sum {α : Type*} [Fintype α]
    (m : ℕ) (d : α → ℕ) (hd : ∀ a, d a ≤ 2 ^ m) :
    logVolumeTailFormula m d ∧ capacityDifferenceFormula m d := by
  have htail : logVolumeTailFormula m d := by
    unfold logVolumeTailFormula binGaugeLogVolume
    calc
      ∑ a, Real.log ((Nat.factorial (d a) : ℝ))
          = ∑ a, ∑ k ∈ Finset.range (2 ^ m), if k < d a then Real.log (k + 1) else 0 := by
              refine Finset.sum_congr rfl ?_
              intro a _
              rw [log_factorial_eq_sum_range, sum_range_eq_sum_range_indicator _ _ (hd a)]
      _ = ∑ k ∈ Finset.range (2 ^ m), ∑ a, if k < d a then Real.log (k + 1) else 0 := by
            rw [Finset.sum_comm]
      _ = ∑ k ∈ Finset.range (2 ^ m), (foldBinTailCount d k : ℝ) * Real.log (k + 1) := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            exact sum_indicator_eq_tailCount_mul d k
  refine ⟨htail, ?_⟩
  unfold capacityDifferenceFormula
  calc
    binGaugeLogVolume d
        = ∑ k ∈ Finset.range (2 ^ m), (foldBinTailCount d k : ℝ) * Real.log (k + 1) := by
            simpa [logVolumeTailFormula] using htail
    _ = ∑ k ∈ Finset.range (2 ^ m),
          ((capacityCurve d (k + 1) - capacityCurve d k : ℕ) : ℝ) * Real.log (k + 1) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          have hkpos : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
          have hcount :
              (foldBinTailCount d k : ℝ) =
                ((capacityCurve d (k + 1) - capacityCurve d k : ℕ) : ℝ) := by
            exact congrArg (fun n : ℕ => (n : ℝ))
              (by simpa [foldBinTailCount, deltaCapacity] using
                (deltaCapacity_eq_card_ge d (k + 1) hkpos).symm)
          rw [hcount]

end Omega.Folding
