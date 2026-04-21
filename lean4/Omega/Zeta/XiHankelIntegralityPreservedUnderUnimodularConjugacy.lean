import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

open Matrix

/-- Rational square matrices in the Hankel chapter. -/
abbrev XiHankelMatrix (d : ℕ) := Matrix (Fin d) (Fin d) ℚ

/-- Entrywise integrality for a rational matrix. -/
def HasIntegerEntries {d : ℕ} (A : XiHankelMatrix d) : Prop :=
  ∀ i j, ∃ z : ℤ, A i j = z

private lemma hasIntegerEntries_mul {d : ℕ} {A B : XiHankelMatrix d}
    (hA : HasIntegerEntries A) (hB : HasIntegerEntries B) :
    HasIntegerEntries (A * B) := by
  intro i j
  classical
  choose a ha using fun k : Fin d => hA i k
  choose b hb using fun k : Fin d => hB k j
  refine ⟨∑ k, a k * b k, ?_⟩
  calc
    (A * B) i j = ∑ k, A i k * B k j := by simp [Matrix.mul_apply]
    _ = ∑ k, ((a k : ℤ) : ℚ) * ((b k : ℤ) : ℚ) := by simp [ha, hb]
    _ = ((∑ k, a k * b k : ℤ) : ℚ) := by simp

/-- If a rational Hankel matrix becomes integral after conjugation by an integer unimodular change
of basis, then the original matrix was already integral. The proof rewrites
`A = P * (P⁻¹ A P) * P⁻¹` and closes under multiplication of integer-entry matrices.
    prop:xi-hankel-integrality-preserved-under-unimodular-conjugacy -/
theorem paper_xi_hankel_integrality_preserved_under_unimodular_conjugacy {d : ℕ}
    (A P Pinv : XiHankelMatrix d) (hP : HasIntegerEntries P) (hPinv : HasIntegerEntries Pinv)
    (hConj : HasIntegerEntries (Pinv * A * P)) (hUnit : P * Pinv = 1) :
    HasIntegerEntries A := by
  have hRewrite : A = P * (Pinv * A * P) * Pinv := by
    calc
      A = 1 * A * 1 := by simp
      _ = (P * Pinv) * A * (P * Pinv) := by rw [hUnit]
      _ = P * (Pinv * A * P) * Pinv := by simp [Matrix.mul_assoc]
  have hLeft : HasIntegerEntries (P * (Pinv * A * P)) := hasIntegerEntries_mul hP hConj
  have hAll : HasIntegerEntries (P * (Pinv * A * P) * Pinv) := hasIntegerEntries_mul hLeft hPinv
  rw [hRewrite]
  exact hAll

end Omega.Zeta
