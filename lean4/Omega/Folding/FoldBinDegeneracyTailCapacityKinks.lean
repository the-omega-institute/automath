import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Folding.Entropy

namespace Omega.Folding

noncomputable section

/-- Concrete container for the scaled tail/capacity kink package. -/
structure FoldBinDegeneracyTailCapacityKinksData where
  dummy : Unit := ()

/-- The scaled tail observable for the two-level bin-fold degeneracy model. -/
noncomputable def foldBinDegeneracyScaledTail (m : ℕ) (s : ℝ) : ℝ :=
  if s ≤ Real.goldenRatio⁻¹ then 1
  else if s ≤ 1 then (Nat.fib (m + 1) : ℝ) / (Nat.fib (m + 2) : ℝ)
  else 0

/-- The limiting tail profile, with rigid kinks at `φ⁻¹` and `1`. -/
noncomputable def foldBinDegeneracyTailLimitFn (s : ℝ) : ℝ :=
  if s ≤ Real.goldenRatio⁻¹ then 1 else if s ≤ 1 then Real.goldenRatio⁻¹ else 0

/-- The scaled capacity observable for the same two-level model. -/
noncomputable def foldBinDegeneracyScaledCapacity (m : ℕ) (s : ℝ) : ℝ :=
  ((Nat.fib (m + 1) : ℝ) * Real.goldenRatio ^ (-(m : ℝ))) * min 1 s +
    ((Nat.fib m : ℝ) * Real.goldenRatio ^ (-(m : ℝ))) * min (Real.goldenRatio⁻¹) s

/-- The limiting piecewise-linear capacity profile. -/
noncomputable def foldBinDegeneracyCapacityLimitFn (s : ℝ) : ℝ :=
  Real.goldenRatio / Real.sqrt 5 * min 1 s +
    (Real.sqrt 5)⁻¹ * min (Real.goldenRatio⁻¹) s

private lemma phi_inv_lt_one : (Real.goldenRatio⁻¹ : ℝ) < 1 := by
  have hinv : (Real.goldenRatio⁻¹ : ℝ) = Real.goldenRatio - 1 := by
    have hconj : Real.goldenRatio⁻¹ = -Real.goldenConj := by
      simpa [one_div] using Real.inv_goldenRatio
    nlinarith [hconj, Real.goldenRatio_add_goldenConj]
  rw [hinv]
  nlinarith [Real.goldenRatio_lt_two]

private lemma fib_succ_ratio_tendsto_phi_inv :
    Filter.Tendsto (fun m : ℕ => (Nat.fib (m + 1) : ℝ) / (Nat.fib (m + 2) : ℝ))
      Filter.atTop (nhds (Real.goldenRatio⁻¹)) := by
  have hratio := Omega.Entropy.fib_ratio_tendsto_golden
  have hInv :
      Filter.Tendsto
        (fun m : ℕ => ((Nat.fib (m + 2) : ℝ) / (Nat.fib (m + 1) : ℝ))⁻¹)
        Filter.atTop (nhds (Real.goldenRatio⁻¹)) := by
    simpa [one_div] using hratio.inv₀ Real.goldenRatio_ne_zero
  refine hInv.congr' ?_
  exact Filter.Eventually.of_forall fun m => by
    have hfib_ne : ((Nat.fib (m + 1) : ℝ) ≠ 0) := by
      have hfib_pos : 0 < (Nat.fib (m + 1) : ℝ) := by
        exact_mod_cast Nat.fib_pos.mpr (Nat.succ_pos _)
      exact ne_of_gt hfib_pos
    field_simp [hfib_ne]

private lemma fib_succ_mul_phi_neg_tendsto :
    Filter.Tendsto
      (fun m : ℕ => (Nat.fib (m + 1) : ℝ) * Real.goldenRatio ^ (-(m : ℝ)))
      Filter.atTop (nhds (Real.goldenRatio / Real.sqrt 5)) := by
  have hshift :
      Filter.Tendsto
        (fun m : ℕ => (Nat.fib (m + 1) : ℝ) * (Real.goldenRatio ^ (m + 1))⁻¹)
        Filter.atTop (nhds ((Real.sqrt 5)⁻¹)) := by
    simpa [Function.comp] using
      Omega.Entropy.fib_mul_phi_neg_tendsto_inv_sqrt5.comp (Filter.tendsto_add_atTop_nat 1)
  have hEq :
      (fun m : ℕ => (Nat.fib (m + 1) : ℝ) * Real.goldenRatio ^ (-(m : ℝ))) =ᶠ[Filter.atTop]
        fun m : ℕ =>
          Real.goldenRatio * ((Nat.fib (m + 1) : ℝ) * (Real.goldenRatio ^ (m + 1))⁻¹) := by
    exact Filter.Eventually.of_forall fun m => by
      have hpow :
          Real.goldenRatio ^ (-(m : ℝ)) =
            Real.goldenRatio * (Real.goldenRatio ^ (m + 1))⁻¹ := by
        rw [Real.rpow_neg Real.goldenRatio_pos.le, Real.rpow_natCast]
        field_simp [pow_ne_zero (m + 1) Real.goldenRatio_ne_zero]
        ring
      calc
        (Nat.fib (m + 1) : ℝ) * Real.goldenRatio ^ (-(m : ℝ)) =
            (Nat.fib (m + 1) : ℝ) *
              (Real.goldenRatio * (Real.goldenRatio ^ (m + 1))⁻¹) := by rw [hpow]
        _ = Real.goldenRatio * ((Nat.fib (m + 1) : ℝ) * (Real.goldenRatio ^ (m + 1))⁻¹) := by
            ring
  refine Filter.Tendsto.congr' hEq.symm ?_
  simpa [one_div, mul_comm, mul_left_comm, mul_assoc] using hshift.const_mul Real.goldenRatio

namespace FoldBinDegeneracyTailCapacityKinksData

/-- Pointwise scaled tail limit away from the rigid kink locations. -/
def tailLimit (_D : FoldBinDegeneracyTailCapacityKinksData) : Prop :=
  ∀ s : ℝ, s ≠ Real.goldenRatio⁻¹ → s ≠ 1 →
    Filter.Tendsto (fun m : ℕ => foldBinDegeneracyScaledTail m s) Filter.atTop
      (nhds (foldBinDegeneracyTailLimitFn s))

/-- Pointwise scaled capacity limit with the same two kink locations. -/
def capacityLimit (_D : FoldBinDegeneracyTailCapacityKinksData) : Prop :=
  ∀ s : ℝ, 0 ≤ s →
    Filter.Tendsto (fun m : ℕ => foldBinDegeneracyScaledCapacity m s) Filter.atTop
      (nhds (foldBinDegeneracyCapacityLimitFn s))

end FoldBinDegeneracyTailCapacityKinksData

/-- Paper label: `prop:fold-bin-degeneracy-tail-capacity-kinks`. The normalized tail spectrum has
the rigid values `1`, `φ⁻¹`, `0` between the thresholds `φ⁻¹` and `1`, and the capacity profile
converges to the corresponding piecewise-linear limit. -/
theorem paper_fold_bin_degeneracy_tail_capacity_kinks (D : FoldBinDegeneracyTailCapacityKinksData) :
    D.tailLimit ∧ D.capacityLimit := by
  refine ⟨?_, ?_⟩
  · intro s hs_phi hs_one
    by_cases hslt : s < Real.goldenRatio⁻¹
    · have hsle : s ≤ Real.goldenRatio⁻¹ := hslt.le
      have hconst : (fun m : ℕ => foldBinDegeneracyScaledTail m s) = fun _ : ℕ => 1 := by
        funext m
        show foldBinDegeneracyScaledTail m s = 1
        unfold foldBinDegeneracyScaledTail
        exact if_pos hsle
      have hlim : foldBinDegeneracyTailLimitFn s = 1 := by
        show foldBinDegeneracyTailLimitFn s = 1
        unfold foldBinDegeneracyTailLimitFn
        exact if_pos hsle
      rw [hconst]
      simpa [hlim] using (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) _ _)
    · have hge : Real.goldenRatio⁻¹ < s := by
        exact lt_of_le_of_ne (le_of_not_gt hslt) (Ne.symm hs_phi)
      by_cases hslt_one : s < 1
      · have hconst :
          (fun m : ℕ => foldBinDegeneracyScaledTail m s) =
            fun m : ℕ => (Nat.fib (m + 1) : ℝ) / (Nat.fib (m + 2) : ℝ) := by
          funext m
          have hnot_le : ¬ s ≤ Real.goldenRatio⁻¹ := not_le_of_gt hge
          show foldBinDegeneracyScaledTail m s = (Nat.fib (m + 1) : ℝ) / (Nat.fib (m + 2) : ℝ)
          unfold foldBinDegeneracyScaledTail
          rw [if_neg hnot_le, if_pos hslt_one.le]
        have hlim : foldBinDegeneracyTailLimitFn s = Real.goldenRatio⁻¹ := by
          unfold foldBinDegeneracyTailLimitFn
          have hnot_le : ¬ s ≤ Real.goldenRatio⁻¹ := not_le_of_gt hge
          show (if s ≤ Real.goldenRatio⁻¹ then 1 else if s ≤ 1 then Real.goldenRatio⁻¹ else 0) =
              Real.goldenRatio⁻¹
          rw [if_neg hnot_le, if_pos hslt_one.le]
        rw [hconst]
        simpa [hlim] using fib_succ_ratio_tendsto_phi_inv
      · have hone_lt : 1 < s := by
          exact lt_of_le_of_ne (le_of_not_gt hslt_one) (Ne.symm hs_one)
        have hconst : (fun m : ℕ => foldBinDegeneracyScaledTail m s) = fun _ : ℕ => 0 := by
          funext m
          have hnot_le_phi : ¬ s ≤ Real.goldenRatio⁻¹ := not_le_of_gt (lt_trans phi_inv_lt_one hone_lt)
          have hnot_le_one : ¬ s ≤ 1 := not_le_of_gt hone_lt
          show foldBinDegeneracyScaledTail m s = 0
          unfold foldBinDegeneracyScaledTail
          rw [if_neg hnot_le_phi, if_neg hnot_le_one]
        have hlim : foldBinDegeneracyTailLimitFn s = 0 := by
          unfold foldBinDegeneracyTailLimitFn
          have hnot_le_phi : ¬ s ≤ Real.goldenRatio⁻¹ := not_le_of_gt (lt_trans phi_inv_lt_one hone_lt)
          have hnot_le_one : ¬ s ≤ 1 := not_le_of_gt hone_lt
          show (if s ≤ Real.goldenRatio⁻¹ then 1 else if s ≤ 1 then Real.goldenRatio⁻¹ else 0) = 0
          rw [if_neg hnot_le_phi, if_neg hnot_le_one]
        rw [hconst]
        simpa [hlim] using (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) _ _)
  · intro s hs
    unfold foldBinDegeneracyScaledCapacity foldBinDegeneracyCapacityLimitFn
    have h0 := fib_succ_mul_phi_neg_tendsto
    have h1 := Omega.Entropy.fib_mul_phi_neg_tendsto_inv_sqrt5
    simpa [one_div, mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm] using
      (h0.const_mul (min 1 s)).add (h1.const_mul (min (Real.goldenRatio⁻¹) s))

end

end Omega.Folding
