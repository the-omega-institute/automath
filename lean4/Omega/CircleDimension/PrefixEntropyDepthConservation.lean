import Mathlib.Data.Nat.Log
import Mathlib.Tactic
import Omega.CircleDimension.PrefixPrimeLedgerConservation

namespace Omega.CircleDimension

/-- A depth-`b` `d`-channel dyadic prefix address stores `d * b` bits in total. -/
abbrev PrefixAddress (d b : ℕ) := Fin (2 ^ (d * b))

/-- Feasibility of a depth-`b` prefix code on `d` channels. -/
def PrefixFeasible (B : Type*) [Fintype B] (d b : ℕ) : Prop :=
  ∃ enc : B → PrefixAddress d b, Function.Injective enc

/-- The optimal prefix depth is the least `b` such that `2^(d b)` bins can host the finite set. -/
def optimalPrefixDepth (d : ℕ) (B : Type*) [Fintype B] : ℕ :=
  Nat.clog (2 ^ d) (Fintype.card B)

theorem prefixFeasible_of_card_le {B : Type*} [Fintype B] (d b : ℕ)
    (h : Fintype.card B ≤ 2 ^ (d * b)) :
    PrefixFeasible B d b := by
  classical
  let eB : B ≃ Fin (Fintype.card B) := Fintype.equivFin B
  refine ⟨fun x => Fin.castLE h (eB x), ?_⟩
  intro x y hxy
  apply eB.injective
  exact (Fin.castLE_injective h) hxy

theorem optimalPrefixDepth_spec {B : Type*} [Fintype B] (d : ℕ) (hd : 0 < d) :
    PrefixFeasible B d (optimalPrefixDepth d B) := by
  have hbase : 1 < 2 ^ d := by
    simpa using Nat.one_lt_pow hd.ne' (by norm_num : 1 < (2 : ℕ))
  have hcard : Fintype.card B ≤ (2 ^ d) ^ optimalPrefixDepth d B :=
    Nat.le_pow_clog hbase _
  have hcard' : Fintype.card B ≤ 2 ^ (d * optimalPrefixDepth d B) := by
    simpa [optimalPrefixDepth, pow_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hcard
  exact prefixFeasible_of_card_le d (optimalPrefixDepth d B) hcard'

theorem optimalPrefixDepth_min {B : Type*} [Fintype B] (d b : ℕ) (hd : 0 < d)
    (hfeas : PrefixFeasible B d b) :
    optimalPrefixDepth d B ≤ b := by
  rcases hfeas with ⟨enc, henc⟩
  have hcard : Fintype.card B ≤ 2 ^ (d * b) := by
    simpa [PrefixAddress] using (Fintype.card_le_of_injective enc henc)
  have hbase : 1 < 2 ^ d := by
    simpa using Nat.one_lt_pow hd.ne' (by norm_num : 1 < (2 : ℕ))
  have hcard' : Fintype.card B ≤ (2 ^ d) ^ b := by
    simpa [pow_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hcard
  exact (Nat.clog_le_iff_le_pow hbase).2 hcard'

theorem optimalPrefixDepth_is_min {B : Type*} [Fintype B] (d : ℕ) (hd : 0 < d) :
    PrefixFeasible B d (optimalPrefixDepth d B) ∧
      ∀ b, PrefixFeasible B d b → optimalPrefixDepth d B ≤ b := by
  refine ⟨optimalPrefixDepth_spec d hd, ?_⟩
  intro b hfeas
  exact optimalPrefixDepth_min d b hd hfeas

/-- Paper-facing prefix-entropy/depth conservation. If the optimal depth `b*_d(N)` is known to
stay within `1` of `log₂ |B_N| / d`, then any polynomial ball-growth sandwich for `|B_N|` yields
the expected `r / d * log₂ N + O(1)` law for the optimal depth.
    thm:cdim-prefix-entropy-depth-conservation -/
theorem paper_cdim_prefix_entropy_depth_conservation
    (r d : ℕ) (_hd : 0 < d) (ballCard : ℕ → ℕ) (bStar : ℕ → ℕ)
    (hApprox : ∀ N, |(bStar N : ℝ) - realLog2 (ballCard N) / d| ≤ 1)
    (hGrowth : ∃ C : ℝ, ∀ N ≥ 1,
      |realLog2 (ballCard N) / d - ((r : ℝ) / d) * realLog2 N| ≤ C) :
    (∀ N, |(bStar N : ℝ) - realLog2 (ballCard N) / d| ≤ 1) ∧
      ∃ C' : ℝ, ∀ N ≥ 1,
        |(bStar N : ℝ) - ((r : ℝ) / d) * realLog2 N| ≤ C' := by
  rcases hGrowth with ⟨C, hGrowthC⟩
  refine ⟨hApprox, ⟨C + 1, ?_⟩⟩
  intro N hN
  let A : ℝ := (bStar N : ℝ) - realLog2 (ballCard N) / d
  let B : ℝ := realLog2 (ballCard N) / d - ((r : ℝ) / d) * realLog2 N
  have hA : |A| ≤ 1 := by simpa [A] using hApprox N
  have hB : |B| ≤ C := by simpa [B] using hGrowthC N hN
  rcases abs_le.mp hA with ⟨hAlo, hAhi⟩
  rcases abs_le.mp hB with ⟨hBlo, hBhi⟩
  have hSum :
      -(C + 1) ≤ A + B ∧ A + B ≤ C + 1 := by
    constructor <;> linarith
  have hEq : (bStar N : ℝ) - ((r : ℝ) / d) * realLog2 N = A + B := by
    dsimp [A, B]
    ring
  simpa [hEq] using abs_le.mpr hSum

end Omega.CircleDimension
