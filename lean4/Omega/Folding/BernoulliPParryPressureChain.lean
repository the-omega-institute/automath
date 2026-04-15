import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

namespace Omega.Folding

open Matrix

abbrev BernoulliParryState := Fin 4

/-- The `θ = 0` Bernoulli-`p` transfer matrix. -/
def bernoulliParryA0 (p : ℚ) : Matrix BernoulliParryState BernoulliParryState ℚ :=
  !![1 - p, 1 - p, 0, p;
     0, 0, p, 0;
     p, 1, 0, 0;
     1 - p, 0, 0, 0]

/-- Perron right eigenvector for `A₀(p)`. -/
def bernoulliParryRight (p : ℚ) : BernoulliParryState → ℚ :=
  ![1 - p, p ^ 2, p, (1 - p) ^ 2]

/-- Perron left eigenvector for `A₀(p)`. -/
def bernoulliParryLeft (p : ℚ) : BernoulliParryState → ℚ :=
  ![1, 1, p, p]

/-- The Parry-normalized kernel attached to `A₀(p)`. -/
def bernoulliParryKernel (p : ℚ) : Matrix BernoulliParryState BernoulliParryState ℚ :=
  !![1 - p, p ^ 2, 0, p * (1 - p);
     0, 0, 1, 0;
     1 - p, p, 0, 0;
     1, 0, 0, 0]

/-- The stationary distribution of the Parry kernel. -/
def bernoulliParryStationary (p : ℚ) : BernoulliParryState → ℚ :=
  ![(1 - p) / (1 + p ^ 3), p ^ 2 / (1 + p ^ 3), p ^ 2 / (1 + p ^ 3),
    p * (1 - p) ^ 2 / (1 + p ^ 3)]

def leftAction (v : BernoulliParryState → ℚ)
    (A : Matrix BernoulliParryState BernoulliParryState ℚ) : BernoulliParryState → ℚ :=
  fun j => ∑ i, v i * A i j

theorem bernoulliParry_right_eigen (p : ℚ) :
    (bernoulliParryA0 p).mulVec (bernoulliParryRight p) = bernoulliParryRight p := by
  ext i
  fin_cases i <;> simp [bernoulliParryA0, bernoulliParryRight, Matrix.mulVec, dotProduct,
    Fin.sum_univ_four] <;> ring

theorem bernoulliParry_left_eigen (p : ℚ) :
    leftAction (bernoulliParryLeft p) (bernoulliParryA0 p) = bernoulliParryLeft p := by
  ext j
  fin_cases j <;>
    simp [leftAction, bernoulliParryA0, bernoulliParryLeft, Fin.sum_univ_four] <;> ring

theorem bernoulliParry_kernel_eq_conjugation (p : ℚ) (hp : 0 < p) (hp1 : p < 1) :
    ∀ i j,
      bernoulliParryKernel p i j =
        bernoulliParryA0 p i j * bernoulliParryRight p j / bernoulliParryRight p i := by
  have hp0 : p ≠ 0 := by linarith
  have hq0 : 1 - p ≠ 0 := by linarith
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [bernoulliParryKernel, bernoulliParryA0, bernoulliParryRight, hp0, hq0] <;>
    field_simp [hp0, hq0] <;> ring

theorem bernoulliParry_normalizer (p : ℚ) :
    ∑ i, bernoulliParryLeft p i * bernoulliParryRight p i = 1 + p ^ 3 := by
  simp [bernoulliParryLeft, bernoulliParryRight, Fin.sum_univ_four]
  ring

theorem bernoulliParry_stationary_eq_normalized (p : ℚ) :
    ∀ i,
      bernoulliParryStationary p i =
        bernoulliParryLeft p i * bernoulliParryRight p i / (1 + p ^ 3) := by
  intro i
  fin_cases i <;>
    simp [bernoulliParryStationary, bernoulliParryLeft, bernoulliParryRight] <;> ring

theorem bernoulliParry_stationary_left_fixed (p : ℚ) (hp : 0 < p) :
    leftAction (bernoulliParryStationary p) (bernoulliParryKernel p) =
      bernoulliParryStationary p := by
  have hnorm : 1 + p ^ 3 ≠ 0 := by nlinarith [pow_pos hp 3]
  ext j
  fin_cases j <;>
    simp [leftAction, bernoulliParryStationary, bernoulliParryKernel, Fin.sum_univ_four, hnorm] <;>
    field_simp [hnorm] <;> ring

theorem bernoulliParry_stationary_sum (p : ℚ) (hp : 0 < p) :
    ∑ i, bernoulliParryStationary p i = 1 := by
  have hnorm : 1 + p ^ 3 ≠ 0 := by nlinarith [pow_pos hp 3]
  simp [bernoulliParryStationary, Fin.sum_univ_four, hnorm]
  field_simp [hnorm]
  ring

/-- Paper-facing Bernoulli-`p` Parry-kernel package. -/
theorem paper_fold_bernoulli_p_parry_pressure_chain :
    ∀ p : ℚ, 0 < p → p < 1 →
    (bernoulliParryA0 p).mulVec (bernoulliParryRight p) = bernoulliParryRight p ∧
      leftAction (bernoulliParryLeft p) (bernoulliParryA0 p) = bernoulliParryLeft p ∧
      (∀ i j,
        bernoulliParryKernel p i j =
          bernoulliParryA0 p i j * bernoulliParryRight p j / bernoulliParryRight p i) ∧
      (∑ i, bernoulliParryLeft p i * bernoulliParryRight p i = 1 + p ^ 3) ∧
      (∀ i,
        bernoulliParryStationary p i =
          bernoulliParryLeft p i * bernoulliParryRight p i / (1 + p ^ 3)) ∧
      leftAction (bernoulliParryStationary p) (bernoulliParryKernel p) =
        bernoulliParryStationary p ∧
      (∑ i, bernoulliParryStationary p i = 1) := by
  intro p hp hp1
  refine ⟨bernoulliParry_right_eigen p, bernoulliParry_left_eigen p,
    bernoulliParry_kernel_eq_conjugation p hp hp1, bernoulliParry_normalizer p,
    bernoulliParry_stationary_eq_normalized p, bernoulliParry_stationary_left_fixed p hp,
    bernoulliParry_stationary_sum p hp⟩

end Omega.Folding
