import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic
import Omega.POM.BayesInfonceSecondCollisionDominance

open scoped BigOperators

namespace Omega.POM

noncomputable section

/-- The quotient in the pointwise Euclidean division `d(x) = 2^B q_x + s_x`. -/
def infonceRemainderQuotient {X : Type} (B : ℕ) (d : X → ℕ) (x : X) : ℕ :=
  d x / 2 ^ B

/-- The remainder bits in the pointwise Euclidean division `d(x) = 2^B q_x + s_x`. -/
def infonceRemainderBits {X : Type} (B : ℕ) (d : X → ℕ) (x : X) : ℕ :=
  d x % 2 ^ B

/-- The second-order correction after renormalizing the bucket square by `2^B`. -/
def infonceRemainderCorrection {X : Type} (B : ℕ) (d : X → ℕ) (x : X) : ℝ :=
  2 * (infonceRemainderQuotient B d x : ℝ) * (infonceRemainderBits B d x : ℝ) +
    (infonceRemainderBits B d x : ℝ) ^ 2 / ((2 ^ B : ℕ) : ℝ)

/-- Paper label: `thm:pom-infonce-remainder-bits-second-order-renormalization`.
Pointwise Euclidean division expands the renormalized bucket square exactly; summing over the
fibers gives an `O(2^B |X|)` correction bound, and the Bayes-InfoNCE second-collision wrapper
then supplies the asymptotic scaling law. -/
theorem paper_pom_infonce_remainder_bits_second_order_renormalization
    {X : Type} [Fintype X] [DecidableEq X]
    (K B : ℕ) (d : X → ℕ) (qBound : ℝ) (hqBound_nonneg : 0 ≤ qBound)
    (hq : ∀ x, (infonceRemainderQuotient B d x : ℝ) ≤ qBound)
    (Lstar M2 M3 wmax S2 : ℕ → ℝ) (r2 : ℝ)
    (hrepr : ∀ m,
      Lstar m =
        bayesInfonceSecondCollisionMainTerm K (M2 m) +
          bayesInfonceSecondCollisionRemainderCoeff K * M3 m)
    (hM3 : ∀ m, M3 m ≤ wmax m * M2 m)
    (hS2 : ∀ m, S2 m = (4 : ℝ) ^ m * M2 m)
    (hpf : ∀ m, S2 m = r2 ^ m) :
    (∀ x,
      (d x : ℝ) = ((2 ^ B : ℕ) : ℝ) * (infonceRemainderQuotient B d x : ℝ) +
        (infonceRemainderBits B d x : ℝ)) ∧
    (∑ x, (d x : ℝ) ^ 2 / ((2 ^ B : ℕ) : ℝ) =
      ∑ x,
        (((2 ^ B : ℕ) : ℝ) * (infonceRemainderQuotient B d x : ℝ) ^ 2 +
          infonceRemainderCorrection B d x)) ∧
    (∑ x, infonceRemainderCorrection B d x ≤
      (Fintype.card X : ℝ) * (((2 ^ B : ℕ) : ℝ) * (2 * qBound + 1))) ∧
    (∀ m,
      Lstar m ≤
        (((K - 1 : ℝ) * Real.log 2) +
          bayesInfonceSecondCollisionRemainderCoeff K * wmax m) * M2 m) ∧
    (∀ m, M2 m = bayesInfonceExponentialScale r2 m) := by
  let powB : ℕ := 2 ^ B
  let powBR : ℝ := (powB : ℝ)
  have hpowB_pos : 0 < powB := by
    dsimp [powB]
    positivity
  have hpowBR_pos : 0 < powBR := by
    dsimp [powBR]
    positivity
  have hpowBR_ne : powBR ≠ 0 := ne_of_gt hpowBR_pos
  have hsplit :
      ∀ x, (d x : ℝ) = powBR * (infonceRemainderQuotient B d x : ℝ) +
        (infonceRemainderBits B d x : ℝ) := by
    intro x
    have hnat :
        d x = powB * infonceRemainderQuotient B d x + infonceRemainderBits B d x := by
      dsimp [powB]
      simpa [infonceRemainderQuotient, infonceRemainderBits, Nat.add_comm, Nat.mul_comm] using
        (Nat.div_add_mod (d x) (2 ^ B)).symm
    have hnatR := congrArg (fun n : ℕ => (n : ℝ)) hnat
    simpa [powBR, powB] using hnatR
  have hsum_expand :
      ∑ x, (d x : ℝ) ^ 2 / powBR =
        ∑ x,
          (powBR * (infonceRemainderQuotient B d x : ℝ) ^ 2 +
            infonceRemainderCorrection B d x) := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    have hxsplit := hsplit x
    calc
      (d x : ℝ) ^ 2 / powBR =
          (powBR * (infonceRemainderQuotient B d x : ℝ) +
            (infonceRemainderBits B d x : ℝ)) ^ 2 / powBR := by
              rw [hxsplit]
      _ = powBR * (infonceRemainderQuotient B d x : ℝ) ^ 2 +
            infonceRemainderCorrection B d x := by
              unfold infonceRemainderCorrection
              field_simp [hpowBR_ne]
              ring
  have hcorr_bound :
      ∀ x, infonceRemainderCorrection B d x ≤ powBR * (2 * qBound + 1) := by
    intro x
    have hs_lt :
        infonceRemainderBits B d x < powB := by
      dsimp [powB]
      exact Nat.mod_lt _ hpowB_pos
    have hs_nonneg : 0 ≤ (infonceRemainderBits B d x : ℝ) := by positivity
    have hs_le : (infonceRemainderBits B d x : ℝ) ≤ powBR := by
      have hs_nat : infonceRemainderBits B d x ≤ powB := Nat.le_of_lt hs_lt
      have hs_real : ((infonceRemainderBits B d x : ℕ) : ℝ) ≤ (powB : ℝ) := by
        exact_mod_cast hs_nat
      simpa [powBR] using hs_real
    have hsq_div_le_self :
        (infonceRemainderBits B d x : ℝ) ^ 2 / powBR ≤ (infonceRemainderBits B d x : ℝ) := by
      have hsq_le :
          (infonceRemainderBits B d x : ℝ) ^ 2 ≤
            (infonceRemainderBits B d x : ℝ) * powBR := by
        nlinarith
      exact (div_le_iff₀ hpowBR_pos).2 (by
        simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using hsq_le)
    have hsq_div_le_pow :
        (infonceRemainderBits B d x : ℝ) ^ 2 / powBR ≤ powBR := by
      exact le_trans hsq_div_le_self hs_le
    have hqs_le :
        (infonceRemainderQuotient B d x : ℝ) * (infonceRemainderBits B d x : ℝ) ≤
          qBound * powBR := by
      have hmul₁ :
          (infonceRemainderQuotient B d x : ℝ) * (infonceRemainderBits B d x : ℝ) ≤
            qBound * (infonceRemainderBits B d x : ℝ) := by
        exact mul_le_mul_of_nonneg_right (hq x) hs_nonneg
      have hmul₂ :
          qBound * (infonceRemainderBits B d x : ℝ) ≤ qBound * powBR := by
        exact mul_le_mul_of_nonneg_left hs_le hqBound_nonneg
      exact le_trans hmul₁ hmul₂
    unfold infonceRemainderCorrection
    nlinarith
  have hcorr_sum :
      ∑ x, infonceRemainderCorrection B d x ≤
        (Fintype.card X : ℝ) * (powBR * (2 * qBound + 1)) := by
    calc
      ∑ x, infonceRemainderCorrection B d x ≤ ∑ x : X, powBR * (2 * qBound + 1) := by
        refine Finset.sum_le_sum ?_
        intro x hx
        exact hcorr_bound x
      _ = (Fintype.card X : ℝ) * (powBR * (2 * qBound + 1)) := by
        simp
  have hbayes :=
    paper_pom_bayes_infonce_second_collision_dominance K Lstar M2 M3 wmax S2 r2
      hrepr hM3 hS2 hpf
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [powB, powBR] using hsplit
  · simpa [powB, powBR] using hsum_expand
  · simpa [powB, powBR] using hcorr_sum
  · exact hbayes.2.1
  · exact hbayes.2.2

end

end Omega.POM
