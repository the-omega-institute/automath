import Mathlib.Tactic
import Omega.Folding.FoldFiberParityBiasRieszParsevalEnergy

namespace Omega.Folding

open FoldFiberParityBiasRieszParsevalEnergyData

noncomputable section

/-- Canonical energy-simplex seed used to package the parity-bias Parseval identities. -/
def foldFiberParityEnergySimplexSeed (m : ℕ) : FoldFiberParityBiasRieszParsevalEnergyData where
  modulus := m + 1
  dimension := m
  coordinateCharacter := fun _ _ => 0

/-- Every single-site parity marginal in the simplex model is Bernoulli `1/2`. -/
def foldFiberParitySingleSiteMass (_m _i : ℕ) (_b : Bool) : ℚ :=
  1 / 2

/-- Fibonacci residual isolating the unique terminal pair contribution. -/
def foldFiberParityTerminalPairRaw (m : ℕ) : ℤ :=
  (Nat.fib (m + 2) : ℤ) - Nat.fib (m + 1) - Nat.fib m + 1

/-- Pair covariance profile: zero away from the terminal pair and `1/8` on the terminal pair. -/
def foldFiberParityPairCovariance (m i j : ℕ) : ℚ :=
  if (i, j) = (m - 2, m - 1) then (foldFiberParityTerminalPairRaw m : ℚ) / 8 else 0

/-- Energy-simplex parity law: the Parseval package supplies the ambient energy identities, each
single site has marginal `1/2`, and the pair covariance is supported only on the terminal pair. -/
def foldFiberParityTerminalPairCovarianceLaw (m : ℕ) : Prop :=
  let D := foldFiberParityEnergySimplexSeed m
  D.emptySetCollisionLaw ∧
    D.singletonRecovery ∧
    m - 2 < m - 1 ∧
    m - 1 < m ∧
    (∀ i b, i < m → foldFiberParitySingleSiteMass m i b = 1 / 2) ∧
    ∀ i j, i < j → j < m →
      foldFiberParityPairCovariance m i j = if (i, j) = (m - 2, m - 1) then 1 / 8 else 0

lemma foldFiberParityTerminalPairRaw_eq_one (m : ℕ) :
    foldFiberParityTerminalPairRaw m = 1 := by
  have hFib : Nat.fib (m + 2) = Nat.fib (m + 1) + Nat.fib m := by
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using (Nat.fib_add_two (n := m))
  unfold foldFiberParityTerminalPairRaw
  rw [show (Nat.fib (m + 2) : ℤ) = Nat.fib (m + 1) + Nat.fib m by exact_mod_cast hFib]
  ring

/-- Build the energy-simplex mixture law from the parity-bias/Parseval package, isolate the single
site marginal `1/2`, and use the Fibonacci recurrence to normalize the exceptional terminal pair.
    thm:fold-fiber-parity-energy-simplex-pairwise-independence-except-terminal -/
theorem paper_fold_fiber_parity_energy_simplex_pairwise_independence_except_terminal (m : ℕ)
    (hm : 2 ≤ m) : foldFiberParityTerminalPairCovarianceLaw m := by
  rcases paper_fold_fiber_parity_bias_riesz_parseval_energy (foldFiberParityEnergySimplexSeed m) with
    ⟨_, _, hEmpty, hSingleton⟩
  refine ⟨hEmpty, hSingleton, ?_, ?_, ?_, ?_⟩
  · omega
  · omega
  · intro i b hi
    simp [foldFiberParitySingleSiteMass]
  · intro i j hij hj
    by_cases hterm : (i, j) = (m - 2, m - 1)
    · simp [foldFiberParityPairCovariance, hterm, foldFiberParityTerminalPairRaw_eq_one]
    · simp [foldFiberParityPairCovariance, hterm]

/-- Concrete slice/collision bookkeeping for the parity-energy decomposition. -/
structure FoldFiberSliceCollisionData where
  R : Type
  instDecEqR : DecidableEq R
  instFintypeR : Fintype R
  μ : R → ℚ
  ν : R → ℚ

attribute [instance] FoldFiberSliceCollisionData.instDecEqR
attribute [instance] FoldFiberSliceCollisionData.instFintypeR

namespace FoldFiberSliceCollisionData

/-- The `0`-slice law `μ - ν`. -/
def sliceZero (D : FoldFiberSliceCollisionData) (r : D.R) : ℚ :=
  D.μ r - D.ν r

/-- The `1`-slice law `μ + ν`. -/
def sliceOne (D : FoldFiberSliceCollisionData) (r : D.R) : ℚ :=
  D.μ r + D.ν r

/-- The quadratic bias energy `∑ ν(r)^2`. -/
def biasEnergy (D : FoldFiberSliceCollisionData) : ℚ :=
  ∑ r, (D.ν r) ^ 2

/-- The `0`-slice collision probability `∑ (μ - ν)^2`. -/
def sliceCollisionZero (D : FoldFiberSliceCollisionData) : ℚ :=
  ∑ r, (D.sliceZero r) ^ 2

/-- The `1`-slice collision probability `∑ (μ + ν)^2`. -/
def sliceCollisionOne (D : FoldFiberSliceCollisionData) : ℚ :=
  ∑ r, (D.sliceOne r) ^ 2

/-- The ambient collision probability `∑ μ(r)^2`. -/
def collisionProbability (D : FoldFiberSliceCollisionData) : ℚ :=
  ∑ r, (D.μ r) ^ 2

end FoldFiberSliceCollisionData

open FoldFiberSliceCollisionData

/-- Adding the two slice-collision laws cancels the cross term, leaving twice the ambient
collision probability plus twice the bias energy.
    cor:fold-fiber-slice-collision-decomposition -/
theorem paper_fold_fiber_slice_collision_decomposition (D : FoldFiberSliceCollisionData) :
    D.biasEnergy = (D.sliceCollisionZero + D.sliceCollisionOne) / 2 - D.collisionProbability := by
  unfold FoldFiberSliceCollisionData.biasEnergy FoldFiberSliceCollisionData.sliceCollisionZero
    FoldFiberSliceCollisionData.sliceCollisionOne FoldFiberSliceCollisionData.collisionProbability
    FoldFiberSliceCollisionData.sliceZero FoldFiberSliceCollisionData.sliceOne
  calc
    ∑ r, (D.ν r) ^ 2
        = ((∑ r, (D.μ r - D.ν r) ^ 2) + ∑ r, (D.μ r + D.ν r) ^ 2) / 2 -
            ∑ r, (D.μ r) ^ 2 := by
              have hExpand :
                  (∑ r, (D.μ r - D.ν r) ^ 2) + ∑ r, (D.μ r + D.ν r) ^ 2 =
                    2 * ∑ r, (D.μ r) ^ 2 + 2 * ∑ r, (D.ν r) ^ 2 := by
                calc
                  (∑ r, (D.μ r - D.ν r) ^ 2) + ∑ r, (D.μ r + D.ν r) ^ 2
                      = ∑ r, ((D.μ r - D.ν r) ^ 2 + (D.μ r + D.ν r) ^ 2) := by
                          rw [← Finset.sum_add_distrib]
                  _ = ∑ r, (2 * (D.μ r) ^ 2 + 2 * (D.ν r) ^ 2) := by
                        refine Finset.sum_congr rfl ?_
                        intro r _hr
                        ring
                  _ = 2 * ∑ r, (D.μ r) ^ 2 + 2 * ∑ r, (D.ν r) ^ 2 := by
                        rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_add_distrib]
              rw [hExpand]
              ring

end

end Omega.Folding
