import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Multiscale

noncomputable section

/-- The uniform layer average on a finite solenoid approximation. -/
def solenoidLayerMean (n : ℕ) [NeZero n] (f : Fin n → ℝ) : ℝ :=
  (∑ i, f i) / (n : ℝ)

/-- The layer operator that replaces a cylinder function by its layerwise average. -/
def solenoidLayerOperator (n : ℕ) [NeZero n] (f : Fin n → ℝ) : Fin n → ℝ :=
  fun _ => solenoidLayerMean n f

/-- The finite-level variance identity for the uniform stationary measure. -/
def solenoidLayerVariance (n : ℕ) [NeZero n] (f : Fin n → ℝ) : ℝ :=
  ∑ i, f i ^ 2 - (n : ℝ) * (solenoidLayerMean n f) ^ 2

/-- The averaging operator preserves constants, hence it is Markov on each layer. -/
def layerwiseMarkov (n : ℕ) [NeZero n] : Prop :=
  solenoidLayerOperator n (fun _ => (1 : ℝ)) = fun _ => (1 : ℝ)

/-- Jensen/Cauchy-Schwarz gives `L²` contraction for the layerwise averaging operator. -/
def layerwiseL2Contraction (n : ℕ) [NeZero n] : Prop :=
  ∀ f : Fin n → ℝ, ∑ i, (solenoidLayerOperator n f i) ^ 2 ≤ ∑ i, f i ^ 2

/-- Cylinder functions lose all variance after passing to the averaged inverse-limit layer. -/
def inverseLimitVarianceDissipation (n : ℕ) [NeZero n] : Prop :=
  ∀ f : Fin n → ℝ,
    solenoidLayerVariance n (solenoidLayerOperator n f) = 0 ∧
      solenoidLayerVariance n (solenoidLayerOperator n f) ≤ solenoidLayerVariance n f

lemma solenoidLayerMean_mul_card (n : ℕ) [NeZero n] (f : Fin n → ℝ) :
    (n : ℝ) * solenoidLayerMean n f = ∑ i, f i := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  unfold solenoidLayerMean
  calc
    (n : ℝ) * ((∑ i, f i) / (n : ℝ)) = (∑ i, f i) * ((n : ℝ) / (n : ℝ)) := by ring
    _ = ∑ i, f i := by field_simp [hn]

lemma solenoidLayerMean_operator (n : ℕ) [NeZero n] (f : Fin n → ℝ) :
    solenoidLayerMean n (solenoidLayerOperator n f) = solenoidLayerMean n f := by
  have hcard := congrArg (fun x : ℝ => x / (n : ℝ)) (solenoidLayerMean_mul_card n f)
  simpa [solenoidLayerMean, solenoidLayerOperator] using hcard

lemma solenoidLayerOperator_sq_sum_le (n : ℕ) [NeZero n] (f : Fin n → ℝ) :
    ∑ i, (solenoidLayerOperator n f i) ^ 2 ≤ ∑ i, f i ^ 2 := by
  have hn : 0 < (n : ℝ) := by
    exact_mod_cast Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  have hsq :
      (∑ i, f i) ^ 2 ≤ (n : ℝ) * ∑ i, f i ^ 2 := by
    simpa using
      (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i : Fin n => f i))
  have hdiv :
      (∑ i, f i) ^ 2 / (n : ℝ) ≤ ∑ i, f i ^ 2 := by
    exact (div_le_iff₀ hn).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hsq)
  have hnz : (n : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  calc
    ∑ i, (solenoidLayerOperator n f i) ^ 2 = (n : ℝ) * (solenoidLayerMean n f) ^ 2 := by
      simp [solenoidLayerOperator]
    _ = (∑ i, f i) ^ 2 / (n : ℝ) := by
      unfold solenoidLayerMean
      field_simp [hnz]
    _ ≤ ∑ i, f i ^ 2 := hdiv

lemma solenoidLayerVariance_operator (n : ℕ) [NeZero n] (f : Fin n → ℝ) :
    solenoidLayerVariance n (solenoidLayerOperator n f) = 0 := by
  unfold solenoidLayerVariance
  rw [solenoidLayerMean_operator]
  simp [solenoidLayerOperator]

lemma solenoidLayerVariance_nonneg (n : ℕ) [NeZero n] (f : Fin n → ℝ) :
    0 ≤ solenoidLayerVariance n f := by
  have hcontr := solenoidLayerOperator_sq_sum_le n f
  have hconst :
      ∑ i, (solenoidLayerOperator n f i) ^ 2 = (n : ℝ) * (solenoidLayerMean n f) ^ 2 := by
    simp [solenoidLayerOperator]
  rw [solenoidLayerVariance]
  nlinarith [hcontr, hconst]

/-- The uniform layer-average operator is Markov, contracts `L²`, and annihilates the
finite-level variance on cylinder functions.
    prop:app-solenoid-stokes-markov-variance-dissipation -/
theorem paper_app_solenoid_stokes_markov_variance_dissipation (n : ℕ) [NeZero n] :
    layerwiseMarkov n ∧ layerwiseL2Contraction n ∧ inverseLimitVarianceDissipation n := by
  refine ⟨?_, ?_, ?_⟩
  · unfold layerwiseMarkov solenoidLayerOperator solenoidLayerMean
    funext i
    simp
  · intro f
    exact solenoidLayerOperator_sq_sum_le n f
  · intro f
    refine ⟨solenoidLayerVariance_operator n f, ?_⟩
    rw [solenoidLayerVariance_operator]
    exact solenoidLayerVariance_nonneg n f

end

end Omega.Multiscale
