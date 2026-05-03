import Omega.Zeta.XiChainIdempotentStarSaturationComparableGcd

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-prime-register-comparable-idempotent-gcd-band`.
Conclusion-facing restatement of the comparable-chain idempotent product and gcd collapse. -/
theorem paper_conclusion_prime_register_comparable_idempotent_gcd_band {n : ℕ}
    (F G : Finset (Fin n)) (hcomp : F ⊆ G ∨ G ⊆ F) :
    Omega.Zeta.chainIdempotentProduct F G = F ∩ G ∧
      Omega.Zeta.chainIdempotentProduct G F = F ∩ G ∧
      Omega.Zeta.primeSupportProduct (Omega.Zeta.chainIdempotentProduct F G) =
        Nat.gcd (Omega.Zeta.primeSupportProduct F) (Omega.Zeta.primeSupportProduct G) ∧
      Omega.Zeta.chainIdempotentProduct F G = F ∩ G := by
  have hFG := Omega.Zeta.paper_xi_chain_idempotent_star_saturation_comparable_gcd F G hcomp
  have hGF :
      Omega.Zeta.chainIdempotentProduct G F = G ∩ F ∧
        Omega.Zeta.primeSupportProduct (G ∩ F) =
          Nat.gcd (Omega.Zeta.primeSupportProduct G) (Omega.Zeta.primeSupportProduct F) := by
    exact Omega.Zeta.paper_xi_chain_idempotent_star_saturation_comparable_gcd G F
      (hcomp.symm)
  refine ⟨hFG.1, ?_, ?_, hFG.1⟩
  · rw [hGF.1, Finset.inter_comm]
  · rw [hFG.1]
    exact hFG.2

end Omega.Conclusion
