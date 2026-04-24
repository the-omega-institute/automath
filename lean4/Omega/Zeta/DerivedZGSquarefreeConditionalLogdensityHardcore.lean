import Omega.Zeta.DerivedZGHardcoreFactorization

namespace Omega.Zeta

/-- Paper label: `thm:derived-zg-squarefree-conditional-logdensity-hardcore`.
The stabilized ZG Dirichlet value factors through the Euler quotient and the hard-core constant, so
dividing by the squarefree Euler quotient recovers the hard-core constant itself. -/
theorem paper_derived_zg_squarefree_conditional_logdensity_hardcore
    (σ : ℕ) (hsigma : 1 ≤ σ) (prime : ℕ → ℕ) (hprime : ∀ i : ℕ, 2 ≤ prime i) (support : ℕ) :
    let D : DerivedZGHardcoreFactorizationData :=
      { σ := σ, sigma_pos := hsigma, prime := prime, prime_ge_two := hprime, support := support }
    0 < D.hardcoreLimit ∧
      D.hardcoreLimit ≤ 1 ∧
      D.dirichletValue / D.zetaEulerQuotient = D.hardcoreLimit := by
  dsimp
  let D : DerivedZGHardcoreFactorizationData :=
    { σ := σ, sigma_pos := hsigma, prime := prime, prime_ge_two := hprime, support := support }
  have hFactorization := paper_derived_zg_hardcore_factorization D
  rcases hFactorization with ⟨_, _, _, _, _, hHardcorePos, hHardcoreLe, hValue⟩
  have hZetaPos : 0 < D.zetaEulerQuotient := by
    unfold DerivedZGHardcoreFactorizationData.zetaEulerQuotient
      DerivedZGHardcoreFactorizationData.finiteZetaQuotient
    refine Finset.prod_pos ?_
    intro i hi
    have hPrimePos : 0 < (prime i : ℝ) := by
      exact_mod_cast lt_of_lt_of_le (by decide : 0 < 2) (hprime i)
    have hPowPos : 0 < (prime i : ℝ) ^ σ := by positivity
    positivity
  have hZetaNe : D.zetaEulerQuotient ≠ 0 := ne_of_gt hZetaPos
  refine ⟨hHardcorePos, hHardcoreLe, ?_⟩
  calc
    D.dirichletValue / D.zetaEulerQuotient =
        (D.zetaEulerQuotient * D.hardcoreLimit) / D.zetaEulerQuotient := by rw [hValue]
    _ = D.hardcoreLimit := by field_simp [hZetaNe]

end Omega.Zeta
