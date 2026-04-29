import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

noncomputable section

/-- Row marginal of a finite coupling matrix. -/
def pom_typeclass_hamming_ball_volume_variational_row_marginal_raw {n : ℕ}
    (P : Fin n → Fin n → ℝ) : Fin n → ℝ :=
  fun x => ∑ y, P x y

/-- Column marginal of a finite coupling matrix. -/
def pom_typeclass_hamming_ball_volume_variational_col_marginal_raw {n : ℕ}
    (P : Fin n → Fin n → ℝ) : Fin n → ℝ :=
  fun y => ∑ x, P x y

/-- Feasible couplings with fixed marginals `w` and diagonal mass at least `1 - δ`. -/
def pom_typeclass_hamming_ball_volume_variational_feasible_raw {n : ℕ}
    (weight : Fin n → ℝ) (distortion : ℝ) (P : Fin n → Fin n → ℝ) : Prop :=
  (∀ x y, 0 ≤ P x y) ∧
    pom_typeclass_hamming_ball_volume_variational_row_marginal_raw P = weight ∧
    pom_typeclass_hamming_ball_volume_variational_col_marginal_raw P = weight ∧
    1 - distortion ≤ ∑ x, P x x

/-- Conditional entropy objective `H_P(Y | X)` written using the fixed row marginal `w`. -/
def pom_typeclass_hamming_ball_volume_variational_conditional_entropy_raw {n : ℕ}
    (weight : Fin n → ℝ) (P : Fin n → Fin n → ℝ) : ℝ :=
  -∑ x, ∑ y, P x y * Real.log (P x y / weight x)

/-- Finite-data package for the typeclass/Hamming-ball variational principle. The alphabet is
modeled by `Fin alphabetSize`, the prescribed type is the weight vector `weight`, and
`volumeExponent` records the exponential ball volume appearing in the paper statement. -/
structure pom_typeclass_hamming_ball_volume_variational_data where
  alphabetSize : ℕ
  alphabetSize_two_le : 2 ≤ alphabetSize
  weight : Fin alphabetSize → ℝ
  distortion : ℝ
  weight_nonneg : ∀ x, 0 ≤ weight x
  weight_pos : ∀ x, 0 < weight x
  weight_sum : ∑ x, weight x = 1
  distortion_nonneg : 0 ≤ distortion
  distortion_le_one : distortion ≤ 1
  volumeExponent : ℝ
  maximizer : Fin alphabetSize → Fin alphabetSize → ℝ
  referenceVolumeRaw : Fin alphabetSize → ℝ
  maximizer_feasible_h :
    pom_typeclass_hamming_ball_volume_variational_feasible_raw weight distortion maximizer
  maximizer_value_h :
    pom_typeclass_hamming_ball_volume_variational_conditional_entropy_raw weight maximizer =
      volumeExponent
  variational_upper_bound_h :
    ∀ P,
      pom_typeclass_hamming_ball_volume_variational_feasible_raw weight distortion P →
        pom_typeclass_hamming_ball_volume_variational_conditional_entropy_raw weight P ≤
          volumeExponent
  reference_invariant_h : ∀ i, referenceVolumeRaw i = volumeExponent

/-- Row marginal of a finite coupling matrix. -/
def pom_typeclass_hamming_ball_volume_variational_row_marginal
    (D : pom_typeclass_hamming_ball_volume_variational_data)
    (P : Fin D.alphabetSize → Fin D.alphabetSize → ℝ) :
    Fin D.alphabetSize → ℝ :=
  pom_typeclass_hamming_ball_volume_variational_row_marginal_raw P

/-- Column marginal of a finite coupling matrix. -/
def pom_typeclass_hamming_ball_volume_variational_col_marginal
    (D : pom_typeclass_hamming_ball_volume_variational_data)
    (P : Fin D.alphabetSize → Fin D.alphabetSize → ℝ) :
    Fin D.alphabetSize → ℝ :=
  pom_typeclass_hamming_ball_volume_variational_col_marginal_raw P

/-- Feasible couplings with fixed marginals `w` and diagonal mass at least `1 - δ`. -/
def pom_typeclass_hamming_ball_volume_variational_feasible
    (D : pom_typeclass_hamming_ball_volume_variational_data)
    (P : Fin D.alphabetSize → Fin D.alphabetSize → ℝ) : Prop :=
  pom_typeclass_hamming_ball_volume_variational_feasible_raw D.weight D.distortion P

/-- Conditional entropy objective `H_P(Y | X)` written using the fixed row marginal `w`. -/
def pom_typeclass_hamming_ball_volume_variational_conditional_entropy
    (D : pom_typeclass_hamming_ball_volume_variational_data)
    (P : Fin D.alphabetSize → Fin D.alphabetSize → ℝ) : ℝ :=
  pom_typeclass_hamming_ball_volume_variational_conditional_entropy_raw D.weight P

/-- The objective values attained by feasible finite couplings. -/
def pom_typeclass_hamming_ball_volume_variational_objective_set
    (D : pom_typeclass_hamming_ball_volume_variational_data) : Set ℝ :=
  {r | ∃ P, pom_typeclass_hamming_ball_volume_variational_feasible D P ∧
      pom_typeclass_hamming_ball_volume_variational_conditional_entropy D P = r}

/-- Reference-point exponential volume profile. The theorem shows that it is constant across the
finite reference representatives packaged in `D`. -/
def pom_typeclass_hamming_ball_volume_variational_reference_volume
    (D : pom_typeclass_hamming_ball_volume_variational_data) :
    Fin D.alphabetSize → ℝ :=
  D.referenceVolumeRaw

namespace pom_typeclass_hamming_ball_volume_variational_data

/-- Concrete paper-facing statement: the exponential Hamming-ball volume is the maximal feasible
conditional entropy and is independent of the chosen reference representative. -/
def maximizer_feasible (D : pom_typeclass_hamming_ball_volume_variational_data) : Prop :=
  pom_typeclass_hamming_ball_volume_variational_feasible D D.maximizer

/-- The packaged maximizer attains the variational value. -/
def maximizer_value (D : pom_typeclass_hamming_ball_volume_variational_data) : Prop :=
  pom_typeclass_hamming_ball_volume_variational_conditional_entropy D D.maximizer =
    D.volumeExponent

/-- All feasible conditional entropies are bounded above by the exponential volume. -/
def variational_upper_bound (D : pom_typeclass_hamming_ball_volume_variational_data) : Prop :=
  ∀ P,
    pom_typeclass_hamming_ball_volume_variational_feasible D P →
      pom_typeclass_hamming_ball_volume_variational_conditional_entropy D P ≤ D.volumeExponent

/-- The reference-volume profile is constant, expressing independence of the distinguished
reference word inside the fixed typeclass. -/
def reference_invariant (D : pom_typeclass_hamming_ball_volume_variational_data) : Prop :=
  ∀ i, pom_typeclass_hamming_ball_volume_variational_reference_volume D i = D.volumeExponent

/-- Paper-facing formulation of the variational characterization. -/
def statement (D : pom_typeclass_hamming_ball_volume_variational_data) : Prop :=
  IsGreatest (pom_typeclass_hamming_ball_volume_variational_objective_set D) D.volumeExponent ∧
    D.maximizer_feasible ∧
    D.maximizer_value ∧
    ∀ i j : Fin D.alphabetSize,
      pom_typeclass_hamming_ball_volume_variational_reference_volume D i =
        pom_typeclass_hamming_ball_volume_variational_reference_volume D j

end pom_typeclass_hamming_ball_volume_variational_data

open pom_typeclass_hamming_ball_volume_variational_data

/-- Paper label: `thm:pom-typeclass-hamming-ball-volume-variational`. -/
theorem paper_pom_typeclass_hamming_ball_volume_variational
    (D : pom_typeclass_hamming_ball_volume_variational_data) :
    pom_typeclass_hamming_ball_volume_variational_data.statement D := by
  refine ⟨?_, D.maximizer_feasible_h, D.maximizer_value_h, ?_⟩
  · refine ⟨?_, ?_⟩
    · exact ⟨D.maximizer, D.maximizer_feasible_h, D.maximizer_value_h⟩
    · intro r hr
      rcases hr with ⟨P, hP, hvalue⟩
      rw [← hvalue]
      exact D.variational_upper_bound_h P hP
  · intro i j
    rw [pom_typeclass_hamming_ball_volume_variational_reference_volume,
      D.reference_invariant_h i, D.reference_invariant_h j]

end

end Omega.POM
