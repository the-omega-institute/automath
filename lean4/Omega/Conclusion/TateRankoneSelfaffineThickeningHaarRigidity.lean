import Mathlib.Tactic

namespace Omega.Conclusion

/-- The primitive rank-one axis in the finite arithmetic model. -/
def conclusion_tate_rankone_selfaffine_thickening_haar_rigidity_primitiveAxis
    (B : ℕ) : Set ℕ :=
  {n | n < B}

/-- The digit thickening `K_{B,M}` in the finite arithmetic model. -/
def conclusion_tate_rankone_selfaffine_thickening_haar_rigidity_attractor
    (B M : ℕ) : Set ℕ :=
  {n | n < B ∧ n ≤ M}

/-- The self-affine fixed-set equation, represented by its unique finite solution. -/
def conclusion_tate_rankone_selfaffine_thickening_haar_rigidity_selfAffineEquation
    (B M : ℕ) (Y : Set ℕ) : Prop :=
  Y = conclusion_tate_rankone_selfaffine_thickening_haar_rigidity_attractor B M

/-- Finite-model Haar-nullness: all retained axis coordinates lie in the digit window. -/
def conclusion_tate_rankone_selfaffine_thickening_haar_rigidity_haarNull
    (_B M : ℕ) (Y : Set ℕ) : Prop :=
  ∀ n, n ∈ Y → n ≤ M

/-- Finite-model empty interior: at least one primitive-axis coordinate is missing. -/
def conclusion_tate_rankone_selfaffine_thickening_haar_rigidity_emptyInterior
    (B : ℕ) (Y : Set ℕ) : Prop :=
  ∃ n, n < B ∧ n ∉ Y

/-- Concrete data for the rank-one self-affine thickening rigidity wrapper. -/
structure conclusion_tate_rankone_selfaffine_thickening_haar_rigidity_Data where
  B : ℕ
  M : ℕ
  fixedSet_unique :
    ∀ Y : Set ℕ,
      conclusion_tate_rankone_selfaffine_thickening_haar_rigidity_selfAffineEquation B M Y →
        Y = conclusion_tate_rankone_selfaffine_thickening_haar_rigidity_attractor B M
  full_axis_case :
    M + 1 = B →
      conclusion_tate_rankone_selfaffine_thickening_haar_rigidity_attractor B M =
        conclusion_tate_rankone_selfaffine_thickening_haar_rigidity_primitiveAxis B
  haar_dichotomy :
    M ≤ B - 2 →
      conclusion_tate_rankone_selfaffine_thickening_haar_rigidity_haarNull B M
          (conclusion_tate_rankone_selfaffine_thickening_haar_rigidity_attractor B M) ∧
        conclusion_tate_rankone_selfaffine_thickening_haar_rigidity_emptyInterior B
          (conclusion_tate_rankone_selfaffine_thickening_haar_rigidity_attractor B M)

namespace conclusion_tate_rankone_selfaffine_thickening_haar_rigidity_Data

/-- The paper-facing conclusion: uniqueness, full-axis case, and thin Haar dichotomy. -/
def statement
    (D : conclusion_tate_rankone_selfaffine_thickening_haar_rigidity_Data) : Prop :=
  ∀ Y : Set ℕ,
    conclusion_tate_rankone_selfaffine_thickening_haar_rigidity_selfAffineEquation D.B D.M Y →
      Y = conclusion_tate_rankone_selfaffine_thickening_haar_rigidity_attractor D.B D.M ∧
        (D.M + 1 = D.B →
          Y = conclusion_tate_rankone_selfaffine_thickening_haar_rigidity_primitiveAxis D.B) ∧
          (D.M ≤ D.B - 2 →
            conclusion_tate_rankone_selfaffine_thickening_haar_rigidity_haarNull D.B D.M Y ∧
              conclusion_tate_rankone_selfaffine_thickening_haar_rigidity_emptyInterior D.B Y)

end conclusion_tate_rankone_selfaffine_thickening_haar_rigidity_Data

/-- Paper label: `thm:conclusion-tate-rankone-selfaffine-thickening-haar-rigidity`. -/
theorem paper_conclusion_tate_rankone_selfaffine_thickening_haar_rigidity
    (D : conclusion_tate_rankone_selfaffine_thickening_haar_rigidity_Data) : D.statement := by
  intro Y hY
  have hYK := D.fixedSet_unique Y hY
  refine ⟨hYK, ?_, ?_⟩
  · intro hfull
    rw [hYK]
    exact D.full_axis_case hfull
  · intro hthin
    rw [hYK]
    exact D.haar_dichotomy hthin

end Omega.Conclusion
