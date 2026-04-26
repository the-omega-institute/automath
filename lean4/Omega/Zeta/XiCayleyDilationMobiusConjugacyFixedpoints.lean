import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

namespace Omega.Zeta

/-- The projective matrix representing the Möbius map. -/
def xiCayleyDilationMatrix : ℝ → Matrix (Fin 2) (Fin 2) ℝ
  | m => !![1 + m, 1 - m; 1 - m, 1 + m]

/-- A Cayley coordinate on the affine chart. -/
noncomputable def xiCayleyAffine (x : ℝ) : ℝ :=
  (1 + x) / (1 - x)

/-- Its inverse on the complementary affine chart. -/
noncomputable def xiCayleyAffineInv (w : ℝ) : ℝ :=
  (w - 1) / (w + 1)

/-- Dilation on the affine coordinate. -/
def xiAffineDilation (m : ℝ) (x : ℝ) : ℝ :=
  m * x

/-- The Cayley-conjugated dilation in Möbius form. -/
noncomputable def xiCayleyDilationMobius (m w : ℝ) : ℝ :=
  ((1 - m) + (1 + m) * w) / ((1 + m) + (1 - m) * w)

/-- The denominator of the Möbius map. -/
def xiCayleyDilationDenom (m w : ℝ) : ℝ :=
  (1 + m) + (1 - m) * w

/-- Closed-form Cayley conjugacy on the affine chart. -/
def xiCayleyDilationClosedFormConjugacy : Prop :=
  ∀ {m w : ℝ}, 0 < m →
    w ≠ -1 →
    1 - xiAffineDilation m (xiCayleyAffineInv w) ≠ 0 →
    xiCayleyAffine (xiAffineDilation m (xiCayleyAffineInv w)) = xiCayleyDilationMobius m w

/-- The Möbius maps form a semigroup wherever the denominators are nonzero. -/
def xiCayleyDilationSemigroupLaw : Prop :=
  ∀ m n : ℝ,
    xiCayleyDilationMatrix m * xiCayleyDilationMatrix n =
      (2 : ℝ) • xiCayleyDilationMatrix (m * n)

/-- The two boundary endpoints `±1` are fixed. -/
def xiCayleyDilationFixedPointDescription : Prop :=
  ∀ {m : ℝ}, 0 < m →
    xiCayleyDilationMobius m 1 = 1 ∧
      xiCayleyDilationMobius m (-1) = -1

private lemma xiCayleyDilation_closed_form {m w : ℝ} (_hm : 0 < m) (hw : w ≠ -1)
    (_hden : 1 - xiAffineDilation m (xiCayleyAffineInv w) ≠ 0) :
    xiCayleyAffine (xiAffineDilation m (xiCayleyAffineInv w)) = xiCayleyDilationMobius m w := by
  unfold xiCayleyAffine xiAffineDilation xiCayleyAffineInv xiCayleyDilationMobius at *
  have hw' : w + 1 ≠ 0 := by
    intro h
    have : w = -1 := by linarith
    exact hw this
  have hnum :
      1 + m * ((w - 1) / (w + 1)) = ((1 - m) + (1 + m) * w) / (w + 1) := by
    field_simp [hw']
    ring
  have hden' :
      1 - m * ((w - 1) / (w + 1)) = ((1 + m) + (1 - m) * w) / (w + 1) := by
    field_simp [hw']
    ring
  rw [hnum, hden']
  field_simp [hw']

private lemma xiCayleyDilation_semigroup :
    xiCayleyDilationSemigroupLaw := by
  intro m n
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [xiCayleyDilationMatrix, Matrix.mul_apply, Fin.sum_univ_two]
    ring

private lemma xiCayleyDilation_fixedpoints {m : ℝ} (hm : 0 < m) :
    xiCayleyDilationMobius m 1 = 1 ∧ xiCayleyDilationMobius m (-1) = -1 := by
  constructor
  · unfold xiCayleyDilationMobius
    field_simp
    ring
  · unfold xiCayleyDilationMobius
    have hm0 : m ≠ 0 := by positivity
    have hnum : 1 - m + ((1 + m) * (-1)) = -2 * m := by ring
    have hden : 1 + m + (1 - m) * (-1) = 2 * m := by ring
    rw [hnum, hden]
    field_simp [hm0]

/-- Paper label: `thm:xi-cayley-dilation-mobius-conjugacy-fixedpoints`.
The dilation semigroup becomes the displayed Möbius semigroup in Cayley coordinates, and the two
boundary points `±1` are fixed. -/
theorem paper_xi_cayley_dilation_mobius_conjugacy_fixedpoints :
    xiCayleyDilationClosedFormConjugacy ∧
      xiCayleyDilationSemigroupLaw ∧
      xiCayleyDilationFixedPointDescription := by
  exact ⟨xiCayleyDilation_closed_form, xiCayleyDilation_semigroup,
    xiCayleyDilation_fixedpoints⟩

end Omega.Zeta
