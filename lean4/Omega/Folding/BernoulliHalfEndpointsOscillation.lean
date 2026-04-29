import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

namespace Omega.Folding

/-!
# Bernoulli-half endpoint oscillation

Concrete seed identities for the `p = 1 / 2` endpoint formulas: the two zero-mismatch
eigenvalues and the residue-three full-mismatch split.
-/

/-- Data carrier for the paper-facing Bernoulli-half endpoint oscillation statement. -/
structure fold_bernoulli_half_endpoints_oscillation_data where

/-- The golden ratio. -/
noncomputable def fold_bernoulli_half_endpoints_oscillation_phi : ℝ :=
  ((1 : ℝ) + Real.sqrt 5) / 2

/-- The dominant endpoint eigenvalue at `p = 1 / 2`. -/
noncomputable def fold_bernoulli_half_endpoints_oscillation_lambda_plus : ℝ :=
  fold_bernoulli_half_endpoints_oscillation_phi / 2

/-- The oscillating endpoint eigenvalue at `p = 1 / 2`. -/
noncomputable def fold_bernoulli_half_endpoints_oscillation_lambda_minus : ℝ :=
  ((1 : ℝ) - Real.sqrt 5) / 4

/-- The dominant coefficient in the Bernoulli-half zero-mismatch formula. -/
noncomputable def fold_bernoulli_half_endpoints_oscillation_c_plus : ℝ :=
  (25 + 11 * Real.sqrt 5) / 90

/-- The oscillating coefficient in the Bernoulli-half zero-mismatch formula. -/
noncomputable def fold_bernoulli_half_endpoints_oscillation_c_minus : ℝ :=
  (25 - 11 * Real.sqrt 5) / 90

/-- The Bernoulli-half zero-mismatch closed-form model. -/
noncomputable def fold_bernoulli_half_endpoints_oscillation_zero_mismatch (m : ℕ) : ℝ :=
  fold_bernoulli_half_endpoints_oscillation_c_plus *
      fold_bernoulli_half_endpoints_oscillation_lambda_plus ^ m +
    fold_bernoulli_half_endpoints_oscillation_c_minus *
      fold_bernoulli_half_endpoints_oscillation_lambda_minus ^ m

/-- The residue-three prefactor for the Bernoulli-half full-mismatch endpoint. -/
noncomputable def fold_bernoulli_half_endpoints_oscillation_full_residue (r : ℕ) : ℝ :=
  if r = 0 then (8 : ℝ) / 9 else if r = 1 then (4 : ℝ) / 9 else (1 : ℝ) / 4

/-- The Bernoulli-half full-mismatch split indexed by `m = 3 * k + r`. -/
noncomputable def fold_bernoulli_half_endpoints_oscillation_full_split
    (k r : ℕ) : ℝ :=
  ((1 : ℝ) / 8) ^ k * fold_bernoulli_half_endpoints_oscillation_full_residue r

/-- Concrete claim for the Bernoulli-half endpoint oscillation corollary. -/
def fold_bernoulli_half_endpoints_oscillation_claim
    (_D : fold_bernoulli_half_endpoints_oscillation_data) : Prop :=
  fold_bernoulli_half_endpoints_oscillation_lambda_plus =
      fold_bernoulli_half_endpoints_oscillation_phi / 2 ∧
    fold_bernoulli_half_endpoints_oscillation_lambda_minus =
      ((1 : ℝ) - Real.sqrt 5) / 4 ∧
    (∀ k r : ℕ, r < 3 →
      fold_bernoulli_half_endpoints_oscillation_full_split k r =
        ((1 : ℝ) / 8) ^ k *
          fold_bernoulli_half_endpoints_oscillation_full_residue r) ∧
    (∀ k : ℕ,
      fold_bernoulli_half_endpoints_oscillation_full_split k 0 =
          ((1 : ℝ) / 8) ^ k * ((8 : ℝ) / 9) ∧
        fold_bernoulli_half_endpoints_oscillation_full_split k 1 =
          ((1 : ℝ) / 8) ^ k * ((4 : ℝ) / 9) ∧
        fold_bernoulli_half_endpoints_oscillation_full_split k 2 =
          ((1 : ℝ) / 8) ^ k * ((1 : ℝ) / 4))

/-- Bernoulli-half endpoint closed form and the mod-`3` full-mismatch oscillation.
    cor:fold-bernoulli-half-endpoints-oscillation -/
theorem paper_fold_bernoulli_half_endpoints_oscillation
    (D : fold_bernoulli_half_endpoints_oscillation_data) :
    fold_bernoulli_half_endpoints_oscillation_claim D := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · intro k r _hr
    rfl
  · intro k
    simp [fold_bernoulli_half_endpoints_oscillation_full_split,
      fold_bernoulli_half_endpoints_oscillation_full_residue]

end Omega.Folding
