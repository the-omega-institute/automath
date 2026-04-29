import Mathlib.Tactic

namespace Omega.OperatorAlgebra

section

variable {OmegaTy : Type*} [Fintype OmegaTy] [DecidableEq OmegaTy]

/-- The genus-`g` contribution of a class of cardinality `n`, written in a concrete piecewise form:
`n²` for `g = 0`, `1` for `g = 1`, and `n^(2-2g) = 1 / n^(2g-2)` for `g ≥ 2`. -/
def derivedCoarseningGenusWeight : Nat → Nat → ℚ
  | 0, n => n ^ 2
  | 1, _ => 1
  | g + 2, n => 1 / (n : ℚ) ^ (2 * g + 2)

/-- Concrete data for one genuine merge step in a finite coarse-graining: two nonempty classes are
merged into a single class of size `|A| + |B|`. -/
structure DerivedCoarseningGenusSignLawData
    (OmegaTy : Type*) [Fintype OmegaTy] [DecidableEq OmegaTy] where
  left : Finset OmegaTy
  right : Finset OmegaTy
  left_nonempty : left.Nonempty
  right_nonempty : right.Nonempty
  disjoint : Disjoint left right

namespace DerivedCoarseningGenusSignLawData

/-- The merged class cardinality appearing in the single-step coarse-graining law. -/
def mergedCard (D : DerivedCoarseningGenusSignLawData OmegaTy) : Nat :=
  D.left.card + D.right.card

/-- Change of the genus partition sum under the merge `A, B ↦ A ⊔ B`. -/
def genusDelta (D : DerivedCoarseningGenusSignLawData OmegaTy) (g : Nat) : ℚ :=
  derivedCoarseningGenusWeight g D.mergedCard -
    derivedCoarseningGenusWeight g D.left.card -
    derivedCoarseningGenusWeight g D.right.card

/-- Sphere gain, torus loss, and higher-genus loss for the audited merge step. -/
def Holds (D : DerivedCoarseningGenusSignLawData OmegaTy) : Prop :=
  D.genusDelta 0 > 0 ∧ D.genusDelta 1 < 0 ∧ ∀ g, 2 ≤ g → D.genusDelta g < 0

end DerivedCoarseningGenusSignLawData

/-- Paper label: `thm:derived-coarsening-genus-sign-law`.
A single genuine merge increases the sphere partition sum, decreases the torus partition sum, and
decreases every higher-genus partition sum as well. -/
theorem paper_derived_coarsening_genus_sign_law {OmegaTy : Type*} [Fintype OmegaTy]
    [DecidableEq OmegaTy] (D : DerivedCoarseningGenusSignLawData OmegaTy) : D.Holds := by
  have hleft_pos_nat : 0 < D.left.card := Finset.card_pos.mpr D.left_nonempty
  have hright_pos_nat : 0 < D.right.card := Finset.card_pos.mpr D.right_nonempty
  have hleft_pos : 0 < (D.left.card : ℚ) := by exact_mod_cast hleft_pos_nat
  have hright_pos : 0 < (D.right.card : ℚ) := by exact_mod_cast hright_pos_nat
  refine ⟨?_, ?_, ?_⟩
  · have hdelta :
      D.genusDelta 0 = 2 * (D.left.card : ℚ) * D.right.card := by
        simp [DerivedCoarseningGenusSignLawData.genusDelta,
          DerivedCoarseningGenusSignLawData.mergedCard, derivedCoarseningGenusWeight]
        ring
    rw [hdelta]
    positivity
  · have hdelta : D.genusDelta 1 = (-1 : ℚ) := by
      simp [DerivedCoarseningGenusSignLawData.genusDelta,
        derivedCoarseningGenusWeight]
    linarith
  · intro g hg
    rcases Nat.exists_eq_add_of_le hg with ⟨k, rfl⟩
    have hmerge_pos_nat : 0 < D.mergedCard := by
      unfold DerivedCoarseningGenusSignLawData.mergedCard
      omega
    have hleft_lt_nat : D.left.card < D.mergedCard := Nat.lt_add_of_pos_right hright_pos_nat
    have hpow_lt :
        (D.left.card : ℚ) ^ (2 * k + 2) < (D.mergedCard : ℚ) ^ (2 * k + 2) := by
      exact pow_lt_pow_left₀ (by exact_mod_cast hleft_lt_nat) (by positivity) (by omega)
    have hrecip_lt :
        1 / (D.mergedCard : ℚ) ^ (2 * k + 2) < 1 / (D.left.card : ℚ) ^ (2 * k + 2) := by
      exact one_div_lt_one_div_of_lt (by positivity) hpow_lt
    have hright_term_pos : 0 < 1 / (D.right.card : ℚ) ^ (2 * k + 2) := by
      positivity
    have hdelta :
        D.genusDelta (k + 2) =
          1 / (D.mergedCard : ℚ) ^ (2 * k + 2) -
            1 / (D.left.card : ℚ) ^ (2 * k + 2) -
            1 / (D.right.card : ℚ) ^ (2 * k + 2) := by
      simp [DerivedCoarseningGenusSignLawData.genusDelta,
        DerivedCoarseningGenusSignLawData.mergedCard, derivedCoarseningGenusWeight]
    have hdelta' :
        D.genusDelta (2 + k) =
          1 / (D.mergedCard : ℚ) ^ (2 * k + 2) -
            1 / (D.left.card : ℚ) ^ (2 * k + 2) -
            1 / (D.right.card : ℚ) ^ (2 * k + 2) := by
      simpa [Nat.add_comm] using hdelta
    rw [hdelta']
    linarith

end

end Omega.OperatorAlgebra
