import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic
import Omega.Zeta.WalshParseval

namespace Omega.Folding

noncomputable section

open Omega
open Omega.Core
open Omega.Zeta.WalshParseval
open scoped BigOperators

/-- The singleton Walsh coefficient attached to coordinate `i`. -/
def hypercubeCoordinateBias (S : Finset (Word n)) (i : Fin n) : ℤ :=
  walshBias (indicatorInt S) ({i} : Finset (Fin n))

/-- The weighted Gödel code length induced by the coordinate biases. -/
def hypercubeGodelLength (S : Finset (Word n)) (p : Fin n → ℕ) : ℝ :=
  ∑ i : Fin n, |(hypercubeCoordinateBias S i : ℝ)| * Real.log (p i)

/-- The Walsh-Parseval square bound for the coordinate-bias vector. -/
def hypercubeBiasSquareBound (S : Finset (Word n)) : Prop :=
  ∑ i : Fin n, hypercubeCoordinateBias S i ^ 2 ≤ (S.card : ℤ) * ((2 : ℤ) ^ n - S.card)

/-- The Cauchy-Schwarz ellipsoid bound for the Gödel code length. -/
def hypercubeGodelLengthEllipsoidBound (S : Finset (Word n)) (p : Fin n → ℕ) : Prop :=
  hypercubeGodelLength S p ≤
    Real.sqrt (∑ i : Fin n, (Real.log (p i)) ^ 2) *
      Real.sqrt ((S.card : ℝ) * ((2 : ℝ) ^ n - S.card))

/-- Weighted singleton Fourier energy, normalized by the ambient `(n - 1)`-dimensional cube
surface factor. -/
def weightedBoundaryEnergy (S : Finset (Word n)) (w : Fin n → Real) : Real :=
  (∑ i : Fin n, w i * (hypercubeCoordinateBias S i : Real) ^ 2) / (2 : Real) ^ (n - 1)

theorem paper_fold_hypercube_bias_ellipsoid_godel_length
    (S : Finset (Word n)) (p : Fin n → ℕ) :
    hypercubeBiasSquareBound S ∧ hypercubeGodelLengthEllipsoidBound S p := by
  classical
  let coeff : Finset (Fin n) → ℤ := walshBias (indicatorInt S)
  let nonemptyCoeffs : Finset (Finset (Fin n)) := Finset.univ.erase ∅
  let singletons : Finset (Finset (Fin n)) :=
    Finset.univ.image fun i : Fin n => ({i} : Finset (Fin n))
  have hIndicatorSq : ∑ w : Word n, indicatorInt S w ^ 2 = (S.card : ℤ) := by
    calc
      ∑ w : Word n, indicatorInt S w ^ 2 = ∑ w : Word n, indicatorInt S w := by
        refine Finset.sum_congr rfl ?_
        intro w _
        exact indicatorInt_sq_eq S w
      _ = (S.card : ℤ) := sum_indicatorInt S
  have hEmpty : coeff ∅ = (S.card : ℤ) := by
    simp [coeff, walshBias, sum_indicatorInt]
  have hParseval : ∑ I : Finset (Fin n), coeff I ^ 2 = (2 : ℤ) ^ n * S.card := by
    simpa [coeff, hIndicatorSq] using parseval_general n (indicatorInt S)
  have hDecompose :
      coeff ∅ ^ 2 + Finset.sum nonemptyCoeffs (fun I => coeff I ^ 2) =
        (2 : ℤ) ^ n * S.card := by
    have hErase :
        Finset.sum nonemptyCoeffs (fun I => coeff I ^ 2) + coeff ∅ ^ 2 =
          ∑ I : Finset (Fin n), coeff I ^ 2 := by
      simpa [coeff, nonemptyCoeffs] using
        (Finset.sum_erase_add (s := (Finset.univ : Finset (Finset (Fin n)))) (a := ∅)
          (by simp))
    rw [add_comm] at hErase
    exact hErase.trans hParseval
  have hNonempty :
      Finset.sum nonemptyCoeffs (fun I => coeff I ^ 2) =
        (S.card : ℤ) * ((2 : ℤ) ^ n - S.card) := by
    have hEmptySq : coeff ∅ ^ 2 = (S.card : ℤ) ^ 2 := by simp [hEmpty]
    nlinarith [hDecompose, hEmptySq]
  have hSingletonSum :
      ∑ i : Fin n, hypercubeCoordinateBias S i ^ 2 =
        Finset.sum singletons (fun I => coeff I ^ 2) := by
    unfold singletons
    rw [Finset.sum_image]
    · refine Finset.sum_congr rfl ?_
      intro i _
      simp [hypercubeCoordinateBias, coeff]
    · intro i _ j _ hij
      have hi : i ∈ ({i} : Finset (Fin n)) := by simp
      have hj : i ∈ ({j} : Finset (Fin n)) := by simpa [hij] using hi
      simpa using hj
  have hSingletonSubset :
      singletons ⊆ nonemptyCoeffs := by
    intro I hI
    rcases Finset.mem_image.mp hI with ⟨i, _, rfl⟩
    simp [nonemptyCoeffs]
  have hSingletonLe :
      Finset.sum singletons (fun I => coeff I ^ 2) ≤
        Finset.sum nonemptyCoeffs (fun I => coeff I ^ 2) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hSingletonSubset ?_
    intro I _ hI
    nlinarith
  have hBiasSquare :
      ∑ i : Fin n, hypercubeCoordinateBias S i ^ 2 ≤
        (S.card : ℤ) * ((2 : ℤ) ^ n - S.card) := by
    rw [hSingletonSum]
    exact hSingletonLe.trans hNonempty.le
  have hBiasSquareReal :
      ∑ i : Fin n, ((hypercubeCoordinateBias S i : ℝ) ^ 2) ≤
        (S.card : ℝ) * ((2 : ℝ) ^ n - S.card) := by
    exact_mod_cast hBiasSquare
  have hAbsSquare :
      ∑ i : Fin n, (|(hypercubeCoordinateBias S i : ℝ)| ^ 2) ≤
        (S.card : ℝ) * ((2 : ℝ) ^ n - S.card) := by
    rw [show (∑ i : Fin n, |(hypercubeCoordinateBias S i : ℝ)| ^ 2) =
        ∑ i : Fin n, ((hypercubeCoordinateBias S i : ℝ) ^ 2) by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [sq_abs]]
    exact hBiasSquareReal
  have hSqrt :
      Real.sqrt (∑ i : Fin n, |(hypercubeCoordinateBias S i : ℝ)| ^ 2) ≤
        Real.sqrt ((S.card : ℝ) * ((2 : ℝ) ^ n - S.card)) := by
    refine Real.sqrt_le_sqrt hAbsSquare
  have hCauchy :
      hypercubeGodelLength S p ≤
        Real.sqrt (∑ i : Fin n, |(hypercubeCoordinateBias S i : ℝ)| ^ 2) *
          Real.sqrt (∑ i : Fin n, (Real.log (p i)) ^ 2) := by
    simpa [hypercubeGodelLength, mul_comm] using
      Real.sum_mul_le_sqrt_mul_sqrt
        (Finset.univ : Finset (Fin n))
        (fun i : Fin n => |(hypercubeCoordinateBias S i : ℝ)|)
        (fun i : Fin n => Real.log (p i))
  refine ⟨hBiasSquare, ?_⟩
  calc
    hypercubeGodelLength S p
        ≤ Real.sqrt (∑ i : Fin n, |(hypercubeCoordinateBias S i : ℝ)| ^ 2) *
            Real.sqrt (∑ i : Fin n, (Real.log (p i)) ^ 2) := hCauchy
    _ ≤ Real.sqrt ((S.card : ℝ) * ((2 : ℝ) ^ n - S.card)) *
          Real.sqrt (∑ i : Fin n, (Real.log (p i)) ^ 2) := by
            exact mul_le_mul_of_nonneg_right hSqrt (Real.sqrt_nonneg _)
    _ = Real.sqrt (∑ i : Fin n, (Real.log (p i)) ^ 2) *
          Real.sqrt ((S.card : ℝ) * ((2 : ℝ) ^ n - S.card)) := by ring

/-- Paper label: `prop:fold-hypercube-weighted-energy-ellipsoid-bias`.
Rearranging the normalized weighted singleton-Fourier energy gives the claimed ellipsoid bound on
the coordinate-bias vector. -/
theorem paper_fold_hypercube_weighted_energy_ellipsoid_bias
    (S : Finset (Omega.Word n)) (w : Fin n → Real) (hw : forall i, 0 < w i) :
    (∑ i : Fin n, w i * (hypercubeCoordinateBias S i : Real) ^ 2) <=
      (2 : Real) ^ (n - 1) * weightedBoundaryEnergy S w := by
  have _ := hw
  have hpowne : (2 : Real) ^ (n - 1) ≠ 0 := by positivity
  have hEq :
      (2 : Real) ^ (n - 1) * weightedBoundaryEnergy S w =
        ∑ i : Fin n, w i * (hypercubeCoordinateBias S i : Real) ^ 2 := by
    unfold weightedBoundaryEnergy
    field_simp [hpowne]
  exact le_of_eq hEq.symm

end

end Omega.Folding
