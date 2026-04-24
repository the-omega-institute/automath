import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic
import Omega.UnitCirclePhaseArithmetic.AppHorizonToeplitzLMI

namespace Omega.DerivedConsequences

open scoped BigOperators

/-- The direct-sum block quadratic form obtained by assembling scalar Toeplitz channels over the
character family `Fin (q + 1)`. -/
def derived_cp_visible_characterwise_single_channel_falsifier_block_quadratic
    (q N : ℕ) (c : Fin (q + 1) → ℝ) (x : Fin (q + 1) → Fin (N + 1) → ℝ) : ℝ :=
  ∑ χ : Fin (q + 1), c χ * ∑ i : Fin (N + 1), x χ i ^ 2

/-- Positivity of the block Toeplitz truncation in the character-split diagonal model. -/
def derived_cp_visible_characterwise_single_channel_falsifier_block_psd
    (q N : ℕ) (c : Fin (q + 1) → ℝ) : Prop :=
  ∀ x : Fin (q + 1) → Fin (N + 1) → ℝ,
    0 ≤ derived_cp_visible_characterwise_single_channel_falsifier_block_quadratic q N c x

/-- Positivity of the scalar Toeplitz truncation in the `χ`-channel. -/
def derived_cp_visible_characterwise_single_channel_falsifier_scalar_psd
    (N : ℕ) (r : ℝ) : Prop :=
  Omega.UnitCirclePhaseArithmetic.app_horizon_toeplitz_lmi_psd N r

/-- A common positive `A_m`-valued measure in the diagonal channel model is just the nonnegative
weight vector itself. -/
def derived_cp_visible_characterwise_single_channel_falsifier_common_measure
    (q : ℕ) (c : Fin (q + 1) → ℝ) : Prop :=
  ∃ μ : Fin (q + 1) → ℝ, (∀ χ, 0 ≤ μ χ) ∧ μ = c

/-- A test vector fully supported on the single channel `χ` and on the zeroth Toeplitz basis
vector. -/
def derived_cp_visible_characterwise_single_channel_falsifier_single_channel_vector
    (q N : ℕ) (χ : Fin (q + 1)) : Fin (q + 1) → Fin (N + 1) → ℝ :=
  fun ψ i => if ψ = χ ∧ i = 0 then 1 else 0

lemma derived_cp_visible_characterwise_single_channel_falsifier_block_to_scalar
    (q N : ℕ) (c : Fin (q + 1) → ℝ)
    (hblock : derived_cp_visible_characterwise_single_channel_falsifier_block_psd q N c)
    (χ : Fin (q + 1)) :
    derived_cp_visible_characterwise_single_channel_falsifier_scalar_psd N (c χ) := by
  intro y
  let x : Fin (q + 1) → Fin (N + 1) → ℝ := fun ψ i => if ψ = χ then y i else 0
  have hx := hblock x
  simpa [derived_cp_visible_characterwise_single_channel_falsifier_scalar_psd,
    Omega.UnitCirclePhaseArithmetic.app_horizon_toeplitz_lmi_psd,
    derived_cp_visible_characterwise_single_channel_falsifier_block_psd,
    derived_cp_visible_characterwise_single_channel_falsifier_block_quadratic, x]
    using hx

lemma derived_cp_visible_characterwise_single_channel_falsifier_scalar_to_block
    (q N : ℕ) (c : Fin (q + 1) → ℝ)
    (hscalar :
      ∀ χ : Fin (q + 1),
        derived_cp_visible_characterwise_single_channel_falsifier_scalar_psd N (c χ)) :
    derived_cp_visible_characterwise_single_channel_falsifier_block_psd q N c := by
  intro x
  unfold derived_cp_visible_characterwise_single_channel_falsifier_block_quadratic
  refine Finset.sum_nonneg ?_
  intro χ hχ
  exact hscalar χ (x χ)

lemma derived_cp_visible_characterwise_single_channel_falsifier_scalar_nonneg
    (N : ℕ) (r : ℝ)
    (hscalar : derived_cp_visible_characterwise_single_channel_falsifier_scalar_psd N r) :
    0 ≤ r := by
  have h0 := hscalar (fun i => if i = 0 then 1 else 0)
  simpa [derived_cp_visible_characterwise_single_channel_falsifier_scalar_psd,
    Omega.UnitCirclePhaseArithmetic.app_horizon_toeplitz_lmi_psd] using h0

lemma derived_cp_visible_characterwise_single_channel_falsifier_single_channel_eval
    (q N : ℕ) (c : Fin (q + 1) → ℝ) (χ : Fin (q + 1)) :
    derived_cp_visible_characterwise_single_channel_falsifier_block_quadratic q N c
        (derived_cp_visible_characterwise_single_channel_falsifier_single_channel_vector q N χ) =
      c χ := by
  classical
  have hinner :
      ∀ ψ : Fin (q + 1),
        ∑ i : Fin (N + 1),
            (derived_cp_visible_characterwise_single_channel_falsifier_single_channel_vector
                q N χ ψ i) ^ 2 =
          if ψ = χ then 1 else 0 := by
    intro ψ
    by_cases hψ : ψ = χ
    · subst hψ
      simp [derived_cp_visible_characterwise_single_channel_falsifier_single_channel_vector]
    · simp [derived_cp_visible_characterwise_single_channel_falsifier_single_channel_vector, hψ]
  simp [derived_cp_visible_characterwise_single_channel_falsifier_block_quadratic, hinner]

/-- The block/scalar PSD equivalence, the common-measure reformulation, and the localized
single-channel negative witness. -/
def derived_cp_visible_characterwise_single_channel_falsifier_statement
    (q : ℕ) (c : Fin (q + 1) → ℝ) : Prop :=
  (∀ N : ℕ,
      derived_cp_visible_characterwise_single_channel_falsifier_block_psd q N c ↔
        ∀ χ : Fin (q + 1),
          derived_cp_visible_characterwise_single_channel_falsifier_scalar_psd N (c χ)) ∧
    ((∀ N : ℕ, ∀ χ : Fin (q + 1),
        derived_cp_visible_characterwise_single_channel_falsifier_scalar_psd N (c χ)) ↔
      derived_cp_visible_characterwise_single_channel_falsifier_common_measure q c) ∧
    ((¬ ∀ N : ℕ, derived_cp_visible_characterwise_single_channel_falsifier_block_psd q N c) →
      ∃ N : ℕ, ∃ χ : Fin (q + 1),
        (∀ ψ : Fin (q + 1), ψ ≠ χ →
          ∀ i : Fin (N + 1),
            derived_cp_visible_characterwise_single_channel_falsifier_single_channel_vector
                q N χ ψ i = 0) ∧
          derived_cp_visible_characterwise_single_channel_falsifier_block_quadratic q N c
              (derived_cp_visible_characterwise_single_channel_falsifier_single_channel_vector
                q N χ) < 0)

/-- Paper label: `cor:derived-cp-visible-characterwise-single-channel-falsifier`. In the diagonal
character decomposition model, block Toeplitz positivity is equivalent to scalar positivity in
every character channel; when positivity fails, a violating vector can be supported entirely on one
character summand. -/
theorem paper_derived_cp_visible_characterwise_single_channel_falsifier
    (q : ℕ) (c : Fin (q + 1) → ℝ) :
    derived_cp_visible_characterwise_single_channel_falsifier_statement q c := by
  refine ⟨?_, ?_, ?_⟩
  · intro N
    constructor
    · intro hblock χ
      exact
        derived_cp_visible_characterwise_single_channel_falsifier_block_to_scalar q N c hblock χ
    · intro hscalar
      exact
        derived_cp_visible_characterwise_single_channel_falsifier_scalar_to_block q N c hscalar
  · constructor
    · intro hall
      refine ⟨c, ?_, rfl⟩
      intro χ
      exact
        derived_cp_visible_characterwise_single_channel_falsifier_scalar_nonneg 0 (c χ)
          (hall 0 χ)
    · rintro ⟨μ, hμ, hμc⟩ N χ
      have hcarath :
          Omega.UnitCirclePhaseArithmetic.app_horizon_toeplitz_lmi_carath (c χ) := by
        rw [← hμc]
        exact hμ χ
      exact (Omega.UnitCirclePhaseArithmetic.paper_app_horizon_toeplitz_lmi (c χ)).mp hcarath |>.1 N
  · intro hnot
    have hnotScalar :
        ¬ ∀ N : ℕ, ∀ χ : Fin (q + 1),
          derived_cp_visible_characterwise_single_channel_falsifier_scalar_psd N (c χ) := by
      intro hallScalar
      apply hnot
      intro N
      exact
        derived_cp_visible_characterwise_single_channel_falsifier_scalar_to_block q N c
          (hallScalar N)
    push_neg at hnotScalar
    rcases hnotScalar with ⟨N, χ, hχ⟩
    have hnegCarath :
        ¬ Omega.UnitCirclePhaseArithmetic.app_horizon_toeplitz_lmi_carath (c χ) := by
      intro hcarath
      exact hχ ((Omega.UnitCirclePhaseArithmetic.paper_app_horizon_toeplitz_lmi (c χ)).mp
        hcarath |>.1 N)
    have hneg : c χ < 0 := by
      have : ¬ 0 ≤ c χ := hnegCarath
      linarith
    refine ⟨N, χ, ?_, ?_⟩
    · intro ψ hψ i
      unfold derived_cp_visible_characterwise_single_channel_falsifier_single_channel_vector
      simp [hψ]
    · rw [derived_cp_visible_characterwise_single_channel_falsifier_single_channel_eval]
      exact hneg

end Omega.DerivedConsequences
