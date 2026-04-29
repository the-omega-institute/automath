import Mathlib.Tactic
import Omega.Folding.BinFold

open scoped BigOperators

namespace Omega.Folding

/-- The `cBinFold` fiber over a stable word, viewed as a finite subset of `{0, …, 2^m - 1}`. -/
private def cBinFiberSet (m : ℕ) (x : Omega.X m) : Finset ℕ :=
  (Finset.range (2 ^ m)).filter (fun N => Omega.cBinFold m N = x)

/-- The normalized bin-fold mass at the stable word `x`. -/
def foldBinMass (m : ℕ) (x : Omega.X m) : ℚ :=
  (Omega.cBinFiberMult m x : ℚ) / (2 ^ m : ℚ)

/-- The uniform mass on the finite stable layer `X_m`. -/
noncomputable def foldBinUniformMass (m : ℕ) : ℚ :=
  1 / Fintype.card (Omega.X m)

/-- Squared `L²` gap between the normalized bin-fold law and the uniform law. -/
noncomputable def foldBinL2GapSq (m : ℕ) : ℚ :=
  ∑ x : Omega.X m, (foldBinMass m x - foldBinUniformMass m) ^ 2

/-- Collision mass of the normalized bin-fold law. -/
noncomputable def foldBinCollisionMass (m : ℕ) : ℚ :=
  ∑ x : Omega.X m, (foldBinMass m x) ^ 2

/-- Column-wise `χ²` divergence of the normalized bin-fold law from the uniform law. -/
noncomputable def foldBinChi2Col (m : ℕ) : ℚ :=
  ∑ x : Omega.X m, (foldBinMass m x - foldBinUniformMass m) ^ 2 / foldBinUniformMass m

/-- The `χ²` divergence is the rescaled collision mass minus `1`. -/
def FoldBinChi2ColIdentity (m : ℕ) : Prop :=
  foldBinChi2Col m = (Fintype.card (Omega.X m) : ℚ) * foldBinCollisionMass m - 1

private theorem cBinFiberMult_sum_eq_pow (m : ℕ) :
    ∑ x : Omega.X m, Omega.cBinFiberMult m x = 2 ^ m := by
  classical
  have hDisjoint : (↑(Finset.univ : Finset (Omega.X m)) : Set (Omega.X m)).PairwiseDisjoint
      (cBinFiberSet m) := by
    intro x _ y _ hxy
    rw [Function.onFun, Finset.disjoint_left]
    intro N hx hy
    exact hxy ((Finset.mem_filter.1 hx).2.symm.trans (Finset.mem_filter.1 hy).2)
  have hUnion : Finset.range (2 ^ m) = (Finset.univ : Finset (Omega.X m)).biUnion (cBinFiberSet m) := by
    ext N
    simp only [Finset.mem_range, Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · intro hN
      refine ⟨Omega.cBinFold m N, ?_⟩
      simp [cBinFiberSet, hN]
    · intro hN
      rcases hN with ⟨x, hx⟩
      exact Finset.mem_range.1 ((Finset.mem_filter.1 hx).1)
  calc
    ∑ x : Omega.X m, Omega.cBinFiberMult m x
        = ∑ x : Omega.X m, (cBinFiberSet m x).card := by
            simp [cBinFiberSet, Omega.cBinFiberMult]
    _ = ((Finset.univ : Finset (Omega.X m)).biUnion (cBinFiberSet m)).card :=
      (Finset.card_biUnion hDisjoint).symm
    _ = (Finset.range (2 ^ m)).card := by rw [hUnion]
    _ = 2 ^ m := Finset.card_range (2 ^ m)

private theorem foldBinMass_sum (m : ℕ) : ∑ x : Omega.X m, foldBinMass m x = 1 := by
  have hpow : (2 ^ m : ℚ) ≠ 0 := by positivity
  have hsumQ : ∑ x : Omega.X m, (Omega.cBinFiberMult m x : ℚ) = (2 ^ m : ℚ) := by
    exact_mod_cast cBinFiberMult_sum_eq_pow m
  calc
    ∑ x : Omega.X m, foldBinMass m x
        = (∑ x : Omega.X m, (Omega.cBinFiberMult m x : ℚ)) / (2 ^ m : ℚ) := by
            simp [foldBinMass, Finset.sum_div]
    _ = 1 := by
      rw [hsumQ]
      field_simp [hpow]

private theorem foldBinUniformMass_sum (m : ℕ) :
    ∑ _x : Omega.X m, foldBinUniformMass m = 1 := by
  have hcard : (Fintype.card (Omega.X m) : ℚ) ≠ 0 := by positivity
  rw [Finset.sum_const, nsmul_eq_mul]
  rw [Finset.card_univ]
  unfold foldBinUniformMass
  field_simp [hcard]

private theorem foldBinChi2Col_term (m : ℕ) (x : Omega.X m) :
    (foldBinMass m x - foldBinUniformMass m) ^ 2 / foldBinUniformMass m =
      (Fintype.card (Omega.X m) : ℚ) * (foldBinMass m x) ^ 2 - 2 * foldBinMass m x +
        foldBinUniformMass m := by
  have hcard : (Fintype.card (Omega.X m) : ℚ) ≠ 0 := by positivity
  unfold foldBinUniformMass
  field_simp [hcard]
  ring

/-- Packaging of the normalized bin-fold law as a `χ²` identity against the uniform column law.
    prop:fold-bin-chi2-col -/
theorem paper_fold_bin_chi2_col (m : ℕ) : FoldBinChi2ColIdentity m := by
  unfold FoldBinChi2ColIdentity foldBinChi2Col
  calc
    ∑ x : Omega.X m, (foldBinMass m x - foldBinUniformMass m) ^ 2 / foldBinUniformMass m
        =
          ∑ x : Omega.X m,
            ((Fintype.card (Omega.X m) : ℚ) * (foldBinMass m x) ^ 2 - 2 * foldBinMass m x +
              foldBinUniformMass m) := by
            apply Finset.sum_congr rfl
            intro x _hx
            exact foldBinChi2Col_term m x
    _ =
          (∑ x : Omega.X m, (Fintype.card (Omega.X m) : ℚ) * (foldBinMass m x) ^ 2) -
            ∑ x : Omega.X m, 2 * foldBinMass m x + ∑ x : Omega.X m, foldBinUniformMass m := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = (Fintype.card (Omega.X m) : ℚ) * foldBinCollisionMass m -
          2 * (∑ x : Omega.X m, foldBinMass m x) + ∑ x : Omega.X m, foldBinUniformMass m := by
            rw [foldBinCollisionMass, ← Finset.mul_sum, ← Finset.mul_sum]
    _ = (Fintype.card (Omega.X m) : ℚ) * foldBinCollisionMass m - 2 * 1 + 1 := by
          rw [foldBinMass_sum, foldBinUniformMass_sum]
    _ = (Fintype.card (Omega.X m) : ℚ) * foldBinCollisionMass m - 1 := by ring

end Omega.Folding
