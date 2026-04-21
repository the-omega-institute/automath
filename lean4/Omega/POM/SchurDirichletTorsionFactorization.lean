import Omega.Zeta.FinitePartDirichletCharacterInversionPrime
import Omega.Zeta.FinitePartDirichletTorsionGaussExpansion

open scoped BigOperators

namespace Omega.POM

/-- Paper-facing Schur/Dirichlet factorization wrapper: the finite torsion polynomial admits the
Gauss--Dirichlet expansion, primitive additive shifts factor through the inverse Dirichlet value,
and prime-modulus character orthogonality recovers each unit-class slice. -/
theorem paper_pom_schur_dirichlet_factorization {q : ℕ} [NeZero q] (hq : Nat.Prime q)
    (χ : DirichletCharacter ℂ q) (hχ : DirichletCharacter.IsPrimitive χ)
    (e : AddChar (ZMod q) ℂ) (N : ℕ) (u : ℕ → ℂ)
    (V : Omega.Zeta.PrimeUnitClass q → ℂ) (r : Omega.Zeta.PrimeUnitClass q) :
    Omega.Zeta.finitePartDirichletTorsionSeries χ e N u =
        Omega.Zeta.finitePartDirichletGaussExpansion χ e N u ∧
      (∀ a : (ZMod q)ˣ, gaussSum χ (e.mulShift a) = χ⁻¹ a * gaussSum χ e) ∧
      (((q : ℂ) - 1)⁻¹) *
          ∑ chi0, Omega.Zeta.gaussDirichletCoeff q V chi0 *
            Omega.Zeta.dirichletCharacterOrthogonality q chi0 r = V r := by
  rcases Omega.Zeta.paper_finite_part_dirichlet_torsion_gauss_expansion χ hχ e N u with
    ⟨hSeries, hShift⟩
  refine ⟨hSeries, hShift, ?_⟩
  exact Omega.Zeta.paper_finite_part_dirichlet_character_inversion_prime hq V r

end Omega.POM
