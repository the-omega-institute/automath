import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic

namespace Omega.POM

/-- The size-`d` Hankel block with shift `shift` cut from an integer sequence. -/
def hankelBlock (d shift : ℕ) (a : ℕ → ℤ) : Matrix (Fin d) (Fin d) ℤ :=
  fun i j => a (i.1 + j.1 + shift)

/-- Clearing the determinant denominator in `H₀⁻¹ H₁` via the adjugate identity. -/
def hankelTransitionDenominatorCleared {d : ℕ} (a : ℕ → ℤ) (A : Matrix (Fin d) (Fin d) ℤ) : Prop :=
  (hankelBlock d 0 a).det • A = (hankelBlock d 0 a).adjugate * hankelBlock d 1 a

/-- If the first Hankel block remains non-singular modulo `p`, then the adjugate identity clears
the denominator in the transition matrix and the reduced principal Hankel block still has full
rank `d`.
    thm:pom-stiff0-hankel-good-reduction-dim-stability -/
theorem paper_pom_stiff0_hankel_good_reduction_dim_stability
    {d p : ℕ} [Fact p.Prime] (a : ℕ → ℤ) (A : Matrix (Fin d) (Fin d) ℤ)
    (hshift : hankelBlock d 1 a = hankelBlock d 0 a * A)
    (hstiff : ¬ ((p : ℤ) ∣ (hankelBlock d 0 a).det)) :
    hankelTransitionDenominatorCleared a A ∧
      IsUnit ((hankelBlock d 0 a).map (Int.castRingHom (ZMod p))).det ∧
      Matrix.rank ((hankelBlock d 0 a).map (Int.castRingHom (ZMod p))) = d := by
  let H0 : Matrix (Fin d) (Fin d) ℤ := hankelBlock d 0 a
  let H1 : Matrix (Fin d) (Fin d) ℤ := hankelBlock d 1 a
  have hshift' : H1 = H0 * A := by
    simpa [H0, H1] using hshift
  have hclear : H0.det • A = H0.adjugate * H1 := by
    calc
      H0.det • A = (H0.det • (1 : Matrix (Fin d) (Fin d) ℤ)) * A := by simp
      _ = (H0.adjugate * H0) * A := by rw [Matrix.adjugate_mul]
      _ = H0.adjugate * (H0 * A) := by rw [Matrix.mul_assoc]
      _ = H0.adjugate * H1 := by rw [hshift']
  let H0bar : Matrix (Fin d) (Fin d) (ZMod p) := H0.map (Int.castRingHom (ZMod p))
  have hdetbar_ne : H0bar.det ≠ 0 := by
    intro hzero
    have hcast : ((H0.det : ℤ) : ZMod p) = 0 := by
      have hzero' := hzero
      change (H0.map (Int.castRingHom (ZMod p))).det = 0 at hzero'
      exact (RingHom.map_det (Int.castRingHom (ZMod p)) H0).trans hzero'
    exact hstiff ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hcast)
  have hdetbar_unit : IsUnit H0bar.det := isUnit_iff_ne_zero.mpr hdetbar_ne
  have hH0bar_unit : IsUnit H0bar := (Matrix.isUnit_iff_isUnit_det (A := H0bar)).2 hdetbar_unit
  have hrank : Matrix.rank H0bar = d := by
    simpa [H0bar] using Matrix.rank_of_isUnit H0bar hH0bar_unit
  exact ⟨by simpa [hankelTransitionDenominatorCleared, H0, H1] using hclear,
    hdetbar_unit, hrank⟩

end Omega.POM
