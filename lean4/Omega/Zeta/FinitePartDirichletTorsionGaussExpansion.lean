import Mathlib.Data.Complex.Basic
import Mathlib.NumberTheory.DirichletCharacter.GaussSum
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

noncomputable section

/-- The finite torsion-side Dirichlet series obtained by summing the additive character values
against the coefficients `u (n + 1) / (n + 1)` over a finite window. -/
def finitePartDirichletTorsionSeries {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (e : AddChar (ZMod q) ℂ) (N : ℕ) (u : ℕ → ℂ) : ℂ :=
  Finset.univ.sum fun a : ZMod q =>
    χ a * (Finset.range N).sum fun n => (u (n + 1) / (n + 1 : ℂ)) * e (a * (n + 1))

/-- The same finite window packaged as a sum of Gauss coefficients. -/
def finitePartDirichletGaussExpansion {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (e : AddChar (ZMod q) ℂ) (N : ℕ) (u : ℕ → ℂ) : ℂ :=
  (Finset.range N).sum fun n =>
    (u (n + 1) / (n + 1 : ℂ)) * gaussSum χ (e.mulShift (n + 1 : ZMod q))

/-- Finite truncations of the Dirichlet torsion series are obtained by swapping the finite sums and
recognizing the inner sums as Gauss sums; for primitive characters, shifting the additive
character multiplies the Gauss sum by the inverse Dirichlet value.
    thm:finite-part-dirichlet-torsion-gauss-expansion -/
theorem paper_finite_part_dirichlet_torsion_gauss_expansion {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : DirichletCharacter.IsPrimitive χ)
    (e : AddChar (ZMod q) ℂ) (N : ℕ) (u : ℕ → ℂ) :
    finitePartDirichletTorsionSeries χ e N u = finitePartDirichletGaussExpansion χ e N u ∧
      ∀ a : (ZMod q)ˣ, gaussSum χ (e.mulShift a) = χ⁻¹ a * gaussSum χ e := by
  refine ⟨?_, ?_⟩
  · unfold finitePartDirichletTorsionSeries finitePartDirichletGaussExpansion gaussSum
    simp_rw [AddChar.mulShift_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp [mul_left_comm, mul_comm]
  · intro a
    simpa using gaussSum_mulShift_of_isPrimitive (e := e) hχ a

end

end Omega.Zeta
