import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Omega.Zeta.XiDepthHankelDeterminantVandermondeSquare

namespace Omega.Zeta

open scoped BigOperators

/-- Finite-atomic moment data with a distinguished smallest atom `amin`. The tail atoms are allowed
to remain in the index set, but their weights vanish, so the moment ratio is exactly the leading
atom. -/
structure XiMomentRatioIdentifiesAminData (k : Nat) where
  atoms : Fin (k + 1) → ℝ
  weights : Fin (k + 1) → ℝ
  amin : ℝ
  atom0_eq : atoms 0 = amin
  tail_weights_zero : ∀ i : Fin k, weights i.succ = 0
  weight0_ne_zero : weights 0 ≠ 0
  amin_ne_zero : amin ≠ 0

namespace XiMomentRatioIdentifiesAminData

/-- The real moment sequence attached to the atomic family. -/
def moment {k : Nat} (D : XiMomentRatioIdentifiesAminData k) (n : Nat) : ℝ :=
  ∑ j, D.weights j * D.atoms j ^ n

/-- The leading contribution of the distinguished atom `amin`. -/
def leadingTerm {k : Nat} (D : XiMomentRatioIdentifiesAminData k) (n : Nat) : ℝ :=
  D.weights 0 * D.amin ^ n

/-- The residual tail after isolating the distinguished atom. -/
def tail {k : Nat} (D : XiMomentRatioIdentifiesAminData k) (n : Nat) : ℝ :=
  ∑ i : Fin k, D.weights i.succ * D.atoms i.succ ^ n

/-- The adjacent moment ratio. -/
noncomputable def momentRatio {k : Nat} (D : XiMomentRatioIdentifiesAminData k) (n : Nat) : ℝ :=
  D.moment (n + 1) / D.moment n

/-- Complexified finite-atomic data, reused to access the chapter's verified Hankel/Vandermonde
package. -/
noncomputable def toXiFiniteAtomicMomentData {k : Nat} (D : XiMomentRatioIdentifiesAminData k) :
    XiFiniteAtomicMomentData (k + 1) where
  weights := fun j => (D.weights j : ℂ)
  nodes := fun j => (D.atoms j : ℂ)
  moments := fun n => ∑ j, (D.weights j : ℂ) * (D.atoms j : ℂ) ^ n
  moments_eq := by
    intro n
    rfl

/-- Paper-facing package: the complex Hankel block factors through the Vandermonde matrix, the real
moments split into a distinguished leading term plus tail, the tail vanishes, and therefore every
adjacent moment ratio is exactly `amin`.
    prop:xi-moment-ratio-identifies-amin -/
def momentRatioIdentifiesAmin {k : Nat} (D : XiMomentRatioIdentifiesAminData k) : Prop :=
  D.toXiFiniteAtomicMomentData.hankelDetFactorsAsVandermondeSquare ∧
    (∀ n, D.moment n = D.leadingTerm n + D.tail n) ∧
    (∀ n, D.tail n = 0) ∧
    (∀ n, D.momentRatio n = D.amin)

theorem moment_eq_leading_plus_tail {k : Nat} (D : XiMomentRatioIdentifiesAminData k) (n : Nat) :
    D.moment n = D.leadingTerm n + D.tail n := by
  have hsplit :
      ∑ j : Fin (k + 1), D.weights j * D.atoms j ^ n =
        D.weights 0 * D.atoms 0 ^ n + ∑ i : Fin k, D.weights i.succ * D.atoms i.succ ^ n := by
    simpa using (Fin.sum_univ_succ (f := fun j : Fin (k + 1) => D.weights j * D.atoms j ^ n))
  calc
    D.moment n = D.weights 0 * D.atoms 0 ^ n + ∑ i : Fin k, D.weights i.succ * D.atoms i.succ ^ n :=
      hsplit
    _ = D.leadingTerm n + D.tail n := by
      simp [leadingTerm, tail, D.atom0_eq]

theorem tail_eq_zero {k : Nat} (D : XiMomentRatioIdentifiesAminData k) (n : Nat) : D.tail n = 0 := by
  simp [tail, D.tail_weights_zero]

theorem moment_eq_leading {k : Nat} (D : XiMomentRatioIdentifiesAminData k) (n : Nat) :
    D.moment n = D.weights 0 * D.amin ^ n := by
  rw [D.moment_eq_leading_plus_tail, D.tail_eq_zero]
  simp [leadingTerm]

theorem momentRatio_eq_amin {k : Nat} (D : XiMomentRatioIdentifiesAminData k) (n : Nat) :
    D.momentRatio n = D.amin := by
  have hm : D.moment n = D.weights 0 * D.amin ^ n := D.moment_eq_leading n
  have hm1 : D.moment (n + 1) = D.weights 0 * D.amin ^ (n + 1) := D.moment_eq_leading (n + 1)
  have hpow : D.amin ^ n ≠ 0 := pow_ne_zero _ D.amin_ne_zero
  have hden : D.weights 0 * D.amin ^ n ≠ 0 := mul_ne_zero D.weight0_ne_zero hpow
  rw [momentRatio, hm1, hm, pow_succ]
  calc
    (D.weights 0 * (D.amin ^ n * D.amin)) / (D.weights 0 * D.amin ^ n)
        = ((D.weights 0 * D.amin ^ n) * D.amin) / (D.weights 0 * D.amin ^ n) := by ring
    _ = D.amin := by
      exact mul_div_cancel_left₀ D.amin hden

end XiMomentRatioIdentifiesAminData

open XiMomentRatioIdentifiesAminData

theorem paper_xi_moment_ratio_identifies_amin (k : Nat) (D : XiMomentRatioIdentifiesAminData k) :
    D.momentRatioIdentifiesAmin := by
  refine ⟨paper_xi_depth_hankel_determinant_vandermonde_square (k + 1) D.toXiFiniteAtomicMomentData,
    ?_, ?_, ?_⟩
  · intro n
    exact D.moment_eq_leading_plus_tail n
  · intro n
    exact D.tail_eq_zero n
  · intro n
    exact D.momentRatio_eq_amin n

end Omega.Zeta
