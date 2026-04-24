import Mathlib.Tactic
import Omega.Folding.MomentBounds

namespace Omega

open scoped BigOperators

/-- The size-biased tail mass of fold-time fibers above threshold `B`, normalized by the total
word count `2^m`. At threshold `0` we set the value to `0` so that the paper-facing scaling bound
remains valid without an auxiliary positivity hypothesis on `B`. -/
noncomputable def foldTimeTailMass (m B : Nat) : Nat :=
  if _hB : B = 0 then
    0
  else
    Finset.sum (Finset.univ.filter fun x : X m => B ≤ X.fiberMultiplicity x) X.fiberMultiplicity

/-- The size-biased tail mass, normalized by the total word count `2^m`. -/
noncomputable def foldTimeTailProb (m B : Nat) : ℚ :=
  (foldTimeTailMass m B : ℚ) / (2 ^ m : ℚ)

/-- The common-denominator form of the normalized `q`-collision sum. -/
noncomputable def foldTimeMomentSum (m q : Nat) : ℚ :=
  (momentSum q m : ℚ) * (2 ^ m : ℚ)

/-- The size-biased tail probability is controlled by the normalized `q`-collision sum through the
standard Markov moment estimate on the fiber-weight distribution.
    cor:fold-time-register-moment-tail-scaling -/
theorem paper_fold_time_register_moment_tail_scaling (m q B : Nat) (hq : 2 <= q) :
    foldTimeTailProb m B <= foldTimeMomentSum m q / (2 ^ m * B ^ (q - 1)) := by
  by_cases hB : B = 0
  · have hq' : q - 1 ≠ 0 := by omega
    simp [foldTimeTailProb, foldTimeTailMass, foldTimeMomentSum, hB, hq']
  · let S : Finset (X m) := Finset.univ.filter fun x : X m => B ≤ X.fiberMultiplicity x
    have hmass :
        foldTimeTailMass m B = Finset.sum S X.fiberMultiplicity := by
      simp [foldTimeTailMass, S, hB]
    have hweighted :
        B ^ (q - 1) * Finset.sum S X.fiberMultiplicity ≤ momentSum q m := by
      calc
        B ^ (q - 1) * Finset.sum S X.fiberMultiplicity
            = Finset.sum S fun x => B ^ (q - 1) * X.fiberMultiplicity x := by
                rw [Finset.mul_sum]
        _ ≤ Finset.sum S fun x => X.fiberMultiplicity x ^ q := by
          refine Finset.sum_le_sum ?_
          intro x hx
          have hxB : B ≤ X.fiberMultiplicity x := (Finset.mem_filter.mp hx).2
          have hpow : B ^ (q - 1) ≤ X.fiberMultiplicity x ^ (q - 1) :=
            Nat.pow_le_pow_left hxB (q - 1)
          have hmul := Nat.mul_le_mul_right (X.fiberMultiplicity x) hpow
          calc
            B ^ (q - 1) * X.fiberMultiplicity x
                ≤ X.fiberMultiplicity x ^ (q - 1) * X.fiberMultiplicity x := by
                    simpa [Nat.mul_comm] using hmul
            _ = X.fiberMultiplicity x ^ q := by
                  rw [show q = (q - 1) + 1 by omega, pow_succ]
                  have hsub : q - 1 + 1 - 1 = q - 1 := by omega
                  simp [hsub, Nat.mul_comm]
        _ ≤ ∑ x : X m, X.fiberMultiplicity x ^ q := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
          intro x _ _
          exact Nat.zero_le _
        _ = momentSum q m := by
          simp [momentSum]
    have hweightedQ :
        (B ^ (q - 1) : ℚ) * ((Finset.sum S X.fiberMultiplicity : Nat) : ℚ) ≤
          (momentSum q m : ℚ) := by
      exact_mod_cast hweighted
    have hBpow_pos : 0 < (B ^ (q - 1) : ℚ) := by
      positivity
    have htail :
        ((Finset.sum S X.fiberMultiplicity : Nat) : ℚ) ≤
          (momentSum q m : ℚ) / (B ^ (q - 1) : ℚ) := by
      exact (le_div_iff₀ hBpow_pos).2
        (by simpa [mul_comm, mul_left_comm, mul_assoc] using hweightedQ)
    have hprob_le :
        (foldTimeTailMass m B : ℚ) / (2 ^ m : ℚ) ≤ (foldTimeTailMass m B : ℚ) := by
      have hmass_nonneg : 0 ≤ (foldTimeTailMass m B : ℚ) := by positivity
      have hpow_ge_one : (1 : ℚ) ≤ (2 ^ m : ℚ) := by
        exact_mod_cast (show 1 ≤ 2 ^ m by
          exact Nat.succ_le_of_lt (pow_pos (by decide : 0 < 2) m))
      have hpow_pos : 0 < (2 ^ m : ℚ) := by positivity
      exact (div_le_iff₀ hpow_pos).2 (by nlinarith)
    have hmoment :
        (momentSum q m : ℚ) / (B ^ (q - 1) : ℚ) =
          foldTimeMomentSum m q / ((2 ^ m : ℚ) * (B ^ (q - 1) : ℚ)) := by
      unfold foldTimeMomentSum
      field_simp
    calc
      foldTimeTailProb m B
          = (foldTimeTailMass m B : ℚ) / (2 ^ m : ℚ) := by
              simp [foldTimeTailProb]
      _ ≤ (foldTimeTailMass m B : ℚ) := hprob_le
      _ = ((Finset.sum S X.fiberMultiplicity : Nat) : ℚ) := by
            rw [hmass]
      _ ≤ (momentSum q m : ℚ) / (B ^ (q - 1) : ℚ) := htail
      _ = foldTimeMomentSum m q / ((2 ^ m : ℚ) * (B ^ (q - 1) : ℚ)) := hmoment

end Omega
