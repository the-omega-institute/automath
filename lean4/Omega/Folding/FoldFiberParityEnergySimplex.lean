import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic
import Omega.Folding.FoldFiberParityBiasRieszParsevalEnergy

namespace Omega.Folding

open FoldFiberParityBiasRieszParsevalEnergyData
open scoped BigOperators

noncomputable section

/-- Canonical energy-simplex seed used to package the parity-bias Parseval identities. -/
def foldFiberParityEnergySimplexSeed (m : ℕ) : FoldFiberParityBiasRieszParsevalEnergyData where
  modulus := m + 1
  dimension := m
  coordinateCharacter := fun _ _ => Complex.I

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

private lemma walsh_factor_sq_norm {m : ℕ} (I : Finset (Fin m)) (j : Fin m) :
    ‖1 + ((((if j ∈ I then (-1 : ℝ) else 1 : ℝ)) : ℂ) * Complex.I)‖ ^ 2 = 2 := by
  rw [Complex.sq_norm]
  by_cases hj : j ∈ I <;> norm_num [hj, Complex.normSq_apply]

private lemma walsh_product_sq_norm {m : ℕ} (I : Finset (Fin m)) :
    ‖∏ j : Fin m, (1 + ((((if j ∈ I then (-1 : ℝ) else 1 : ℝ)) : ℂ) * Complex.I))‖ ^ 2 =
      (2 : ℝ) ^ m := by
  let φ : ℂ →* ℝ :=
    { toFun := Complex.normSq
      map_one' := by simp
      map_mul' := Complex.normSq_mul }
  rw [Complex.sq_norm]
  calc
    Complex.normSq (∏ j : Fin m, (1 + ((((if j ∈ I then (-1 : ℝ) else 1 : ℝ)) : ℂ) * Complex.I)))
        = ∏ j : Fin m, Complex.normSq (1 +
            ((((if j ∈ I then (-1 : ℝ) else 1 : ℝ)) : ℂ) * Complex.I)) := by
            simpa [φ] using
              (Finset.map_prod φ
                (fun j : Fin m => 1 + ((((if j ∈ I then (-1 : ℝ) else 1 : ℝ)) : ℂ) * Complex.I))
                Finset.univ)
    _ = ∏ _j : Fin m, (2 : ℝ) := by
          refine Finset.prod_congr rfl ?_
          intro j _
          rw [Complex.normSq_eq_norm_sq]
          exact walsh_factor_sq_norm I j
    _ = (2 : ℝ) ^ m := by simp

private lemma walsh_transform_sq_norm {m : ℕ} (I : Finset (Fin m)) :
    ‖((2 : ℂ) ^ m)⁻¹ *
        ∏ j : Fin m, (1 + ((((if j ∈ I then (-1 : ℝ) else 1 : ℝ)) : ℂ) * Complex.I))‖ ^ 2 =
      ((2 : ℝ) ^ m)⁻¹ := by
  have hprod := walsh_product_sq_norm I
  have hpow :
      Complex.normSq ((2 : ℂ) ^ m) = ((2 : ℝ) ^ m) ^ 2 := by
    rw [Complex.normSq_eq_norm_sq, Complex.norm_pow, Complex.norm_two]
  have htwo : (2 : ℝ) ^ m ≠ 0 := by
    exact pow_ne_zero _ (by norm_num)
  rw [Complex.sq_norm, Complex.normSq_mul, Complex.normSq_inv, hpow, Complex.normSq_eq_norm_sq,
    hprod, pow_two]
  field_simp [htwo]

private lemma parsevalEnergy_walshSigns_eq {m : ℕ} (I : Finset (Fin m)) :
    (foldFiberParityEnergySimplexSeed m).parsevalEnergy
      ((foldFiberParityEnergySimplexSeed m).walshSigns I) = ((2 : ℝ) ^ m)⁻¹ := by
  simp [FoldFiberParityBiasRieszParsevalEnergyData.parsevalEnergy,
    FoldFiberParityBiasRieszParsevalEnergyData.fourierTransform,
    FoldFiberParityBiasRieszParsevalEnergyData.walshSigns, foldFiberParityEnergySimplexSeed,
    Finset.sum_const, nsmul_eq_mul, Finset.card_range]
  have hprod :
      (∏ b : Fin m, ‖1 + ((((if b ∈ I then (-1 : ℝ) else 1 : ℝ)) : ℂ) * Complex.I)‖) ^ 2 =
        (2 : ℝ) ^ m := by
    simpa [Complex.norm_prod] using walsh_product_sq_norm I
  have hm : (m + 1 : ℝ) ≠ 0 := by positivity
  have htwo : (2 : ℝ) ^ m ≠ 0 := by
    exact pow_ne_zero _ (by norm_num)
  have hcore :
      (((2 : ℝ) ^ m)⁻¹ *
          ∏ b : Fin m, ‖1 + ((((if b ∈ I then (-1 : ℝ) else 1 : ℝ)) : ℂ) * Complex.I)‖) ^ 2 =
        ((2 : ℝ) ^ m)⁻¹ := by
    rw [mul_pow, hprod]
    field_simp [htwo]
  rw [hcore]
  show ((↑m + 1 : ℝ)⁻¹) * ((↑m + 1 : ℝ) * ((2 : ℝ) ^ m)⁻¹) = ((2 : ℝ) ^ m)⁻¹
  calc
    ((↑m + 1 : ℝ)⁻¹) * ((↑m + 1 : ℝ) * ((2 : ℝ) ^ m)⁻¹)
        = (((↑m + 1 : ℝ)⁻¹) * (↑m + 1 : ℝ)) * ((2 : ℝ) ^ m)⁻¹ := by ring
    _ = ((2 : ℝ) ^ m)⁻¹ := by simp [hm]

/-- Summing the Walsh/Parseval energies over the full powerset of parity sign patterns gives the
unit simplex mass.
    cor:fold-fiber-parity-energy-simplex -/
theorem paper_fold_fiber_parity_energy_simplex (m : ℕ) :
    let D := foldFiberParityEnergySimplexSeed m;
    Finset.sum ((Finset.univ : Finset (Fin D.dimension)).powerset)
      (fun I => D.parsevalEnergy (D.walshSigns I)) = 1 := by
  classical
  change Finset.sum ((Finset.univ : Finset (Fin m)).powerset)
      (fun I =>
        (foldFiberParityEnergySimplexSeed m).parsevalEnergy
          ((foldFiberParityEnergySimplexSeed m).walshSigns I)) = 1
  calc
    Finset.sum ((Finset.univ : Finset (Fin m)).powerset) (fun I =>
        (foldFiberParityEnergySimplexSeed m).parsevalEnergy
          ((foldFiberParityEnergySimplexSeed m).walshSigns I))
        = Finset.sum ((Finset.univ : Finset (Fin m)).powerset) (fun _I => ((2 : ℝ) ^ m)⁻¹) := by
            refine Finset.sum_congr rfl ?_
            intro I hI
            exact parsevalEnergy_walshSigns_eq I
    _ = (((Finset.univ : Finset (Fin m)).powerset.card : ℝ)) * ((2 : ℝ) ^ m)⁻¹ := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ = ((2 : ℝ) ^ m) * ((2 : ℝ) ^ m)⁻¹ := by
          rw [Finset.card_powerset, Finset.card_univ, Nat.cast_pow]
          norm_num
    _ = 1 := by
          exact mul_inv_cancel₀ (pow_ne_zero _ (by norm_num))

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

/-- The subset energy entering the parity partition function. -/
def foldFiberParityPartitionEnergy {m : ℕ} (θ : Fin m → ℝ) (I : Finset (Fin m)) : ℝ :=
  (∏ j ∈ I, (Real.sin (θ j)) ^ 2) *
    ∏ j ∈ (Finset.univ : Finset (Fin m)) \ I, (Real.cos (θ j)) ^ 2

/-- The mixed Bernoulli weight obtained by biasing membership in `I` with the fugacity `z`. -/
def foldFiberParityMixtureTerm {m : ℕ} (θ : Fin m → ℝ) (z : ℝ) (I : Finset (Fin m)) : ℝ :=
  (∏ j ∈ I, z * (Real.sin (θ j)) ^ 2) *
    ∏ j ∈ (Finset.univ : Finset (Fin m)) \ I, (Real.cos (θ j)) ^ 2

/-- The parity-energy partition function obtained by summing `z ^ |I| E_{m,I}` over the powerset. -/
def foldFiberParityPartitionFunction {m : ℕ} (θ : Fin m → ℝ) (z : ℝ) : ℝ :=
  Finset.sum ((Finset.univ : Finset (Fin m)).powerset)
    (fun I => z ^ I.card * foldFiberParityPartitionEnergy θ I)

private lemma foldFiberParity_weightedEnergy_eq_mixtureTerm {m : ℕ} (θ : Fin m → ℝ)
    (z : ℝ) (I : Finset (Fin m)) :
    z ^ I.card * foldFiberParityPartitionEnergy θ I = foldFiberParityMixtureTerm θ z I := by
  calc
    z ^ I.card * foldFiberParityPartitionEnergy θ I
        = (∏ j ∈ I, z) *
            ((∏ j ∈ I, (Real.sin (θ j)) ^ 2) *
              ∏ j ∈ (Finset.univ : Finset (Fin m)) \ I, (Real.cos (θ j)) ^ 2) := by
              simp [foldFiberParityPartitionEnergy]
    _ = ((∏ j ∈ I, z) * ∏ j ∈ I, (Real.sin (θ j)) ^ 2) *
          ∏ j ∈ (Finset.univ : Finset (Fin m)) \ I, (Real.cos (θ j)) ^ 2 := by
            ac_rfl
    _ = (∏ j ∈ I, z * (Real.sin (θ j)) ^ 2) *
          ∏ j ∈ (Finset.univ : Finset (Fin m)) \ I, (Real.cos (θ j)) ^ 2 := by
            rw [← Finset.prod_mul_distrib]
    _ = foldFiberParityMixtureTerm θ z I := by
          rfl

/-- Summing the weighted parity energies over the powerset gives the expected finite product, and
the same identity can be read as a mixed Bernoulli product law on subsets.
    prop:fold-fiber-parity-energy-partition-function-mixture -/
theorem paper_fold_fiber_parity_energy_partition_function_mixture
    (m : ℕ) (θ : Fin m → ℝ) (z : ℝ) :
    foldFiberParityPartitionFunction θ z =
      ∏ j : Fin m, ((Real.cos (θ j)) ^ 2 + z * (Real.sin (θ j)) ^ 2) ∧
    foldFiberParityPartitionFunction θ z =
      Finset.sum ((Finset.univ : Finset (Fin m)).powerset)
        (fun I => foldFiberParityMixtureTerm θ z I) := by
  have hMixture :
      foldFiberParityPartitionFunction θ z =
        Finset.sum ((Finset.univ : Finset (Fin m)).powerset)
          (fun I => foldFiberParityMixtureTerm θ z I) := by
    unfold foldFiberParityPartitionFunction
    refine Finset.sum_congr rfl ?_
    intro I hI
    exact foldFiberParity_weightedEnergy_eq_mixtureTerm θ z I
  refine ⟨?_, hMixture⟩
  calc
    foldFiberParityPartitionFunction θ z
        = Finset.sum ((Finset.univ : Finset (Fin m)).powerset)
            (fun I => foldFiberParityMixtureTerm θ z I) :=
            hMixture
    _ = ∏ j : Fin m, ((Real.cos (θ j)) ^ 2 + z * (Real.sin (θ j)) ^ 2) := by
          symm
          simpa [foldFiberParityMixtureTerm, add_comm, add_left_comm, add_assoc, mul_comm,
            mul_left_comm, mul_assoc] using
            (Finset.prod_add
              (fun j : Fin m => z * (Real.sin (θ j)) ^ 2)
              (fun j : Fin m => (Real.cos (θ j)) ^ 2)
              (Finset.univ : Finset (Fin m)))

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
