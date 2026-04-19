import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.SPG.WalshDiscreteStokesHolography

namespace Omega.SPG

open scoped BigOperators

/-- Indicator of a finite subset of the hypercube. -/
def hypercubeIndicator (S : Finset (Omega.Word n)) (ω : Omega.Word n) : ℝ :=
  if ω ∈ S then 1 else 0

/-- The Walsh character attached to `I`, written in the real-valued normalization used by the
weighted Stokes statement. -/
def weightedWalshCharacter (I : Finset (Fin n)) (ω : Omega.Word n) : ℝ :=
  (-1 : ℝ) ^ (Omega.Core.activeBits I ω).card

/-- The weighted Laplacian eigenvalue of the Walsh character indexed by `I`. -/
def weightedWalshEigenvalue (I : Finset (Fin n)) (w : Fin n → ℝ) : ℝ :=
  2 * (∑ i ∈ I, w i)

/-- The boundary `1`-form obtained by normalizing the SPG Stokes integrand by the weighted Walsh
eigenvalue. -/
noncomputable def weightedBoundaryOneForm
    (S : Finset (Omega.Word n)) (I : Finset (Fin n)) (w : Fin n → ℝ)
    (u : BoundaryWords I) : ℝ :=
  (weightedWalshEigenvalue I w)⁻¹ *
    (weightedWalshEigenvalue I w * iteratedDifference (hypercubeIndicator S) I u.1)

/-- The total normalized weighted boundary integral. -/
noncomputable def weightedBoundaryIntegral
    (S : Finset (Omega.Word n)) (I : Finset (Fin n)) (w : Fin n → ℝ) :
    ℝ :=
  ∑ u : BoundaryWords I, weightedBoundaryOneForm S I w u

/-- Concrete publication-facing weighted Walsh-Stokes statement. -/
def HypercubeWeightedWalshStokesStatement
    (S : Finset (Omega.Word n)) (I : Finset (Fin n)) (w : Fin n → ℝ) : Prop :=
  0 < weightedWalshEigenvalue I w ∧
    (∑ ω ∈ S, weightedWalshCharacter I ω) = weightedBoundaryIntegral S I w

lemma weightedWalshEigenvalue_pos {n : ℕ} (I : Finset (Fin n)) (w : Fin n → ℝ) (hI : I.Nonempty)
    (hw : ∀ i, 0 < w i) : 0 < weightedWalshEigenvalue I w := by
  obtain ⟨i, hi⟩ := hI
  have hle : w i ≤ (∑ j ∈ I, w j) := by
    exact Finset.single_le_sum (fun j _ => le_of_lt (hw j)) hi
  have hsum : 0 < (∑ j ∈ I, w j) := lt_of_lt_of_le (hw i) hle
  unfold weightedWalshEigenvalue
  nlinarith

lemma walshBias_indicator_eq_sum {n : ℕ} (S : Finset (Omega.Word n)) (I : Finset (Fin n)) :
    walshBias (hypercubeIndicator S) I = (∑ ω ∈ S, weightedWalshCharacter I ω) := by
  classical
  unfold walshBias hypercubeIndicator weightedWalshCharacter
  calc
    ∑ ω : Omega.Word n, (-1 : ℝ) ^ (Omega.Core.activeBits I ω).card * (if ω ∈ S then 1 else 0)
        = ∑ ω : Omega.Word n, if ω ∈ S then (-1 : ℝ) ^ (Omega.Core.activeBits I ω).card else 0 := by
            refine Finset.sum_congr rfl ?_
            intro ω hω
            by_cases hωS : ω ∈ S <;> simp [hωS]
    _ = ∑ ω ∈ S, (-1 : ℝ) ^ (Omega.Core.activeBits I ω).card := by
      simp

lemma weightedBoundaryIntegral_eq_discreteStokesBoundarySum {n : ℕ}
    (S : Finset (Omega.Word n)) (I : Finset (Fin n)) (w : Fin n → ℝ)
    (hEig : 0 < weightedWalshEigenvalue I w) :
    weightedBoundaryIntegral S I w = discreteStokesBoundarySum (hypercubeIndicator S) I := by
  have hEig0 : weightedWalshEigenvalue I w ≠ 0 := ne_of_gt hEig
  unfold weightedBoundaryIntegral weightedBoundaryOneForm discreteStokesBoundarySum
  refine Finset.sum_congr rfl ?_
  intro u hu
  field_simp [hEig0]

/-- Paper label: `thm:fold-hypercube-weighted-walsh-stokes`. -/
theorem paper_fold_hypercube_weighted_walsh_stokes {n : ℕ} (S : Finset (Omega.Word n))
    (I : Finset (Fin n)) (w : Fin n → ℝ) (hI : I.Nonempty) (hw : ∀ i, 0 < w i) :
    HypercubeWeightedWalshStokesStatement S I w := by
  have hEig : 0 < weightedWalshEigenvalue I w := weightedWalshEigenvalue_pos I w hI hw
  refine ⟨hEig, ?_⟩
  calc
    ∑ ω ∈ S, weightedWalshCharacter I ω = walshBias (hypercubeIndicator S) I := by
      symm
      exact walshBias_indicator_eq_sum S I
    _ = discreteStokesBoundarySum (hypercubeIndicator S) I := by
      exact paper_spg_walsh_discrete_stokes_holography n (hypercubeIndicator S) I
    _ = weightedBoundaryIntegral S I w := by
      symm
      exact weightedBoundaryIntegral_eq_discreteStokesBoundarySum S I w hEig

end Omega.SPG
