import Omega.Zeta.XiChainIdempotentComparableFiniteGcdCollapse

namespace Omega.Zeta

/-- Paper label: `thm:xi-comparable-chain-word-kappa-completeness`. -/
theorem paper_xi_comparable_chain_word_kappa_completeness {n : Nat}
    (F0 : Finset (Fin n)) (letters : List (Finset (Fin n)))
    (hchain : ∀ G ∈ F0 :: letters, ∀ H ∈ F0 :: letters, G ⊆ H ∨ H ⊆ G) :
    letters.foldl Omega.Zeta.chainIdempotentProduct F0 =
        letters.foldl (fun A B => A ∩ B) F0 ∧
      Omega.Zeta.primeSupportProduct
          (letters.foldl Omega.Zeta.chainIdempotentProduct F0) =
        (letters.map Omega.Zeta.primeSupportProduct).foldl Nat.gcd
          (Omega.Zeta.primeSupportProduct F0) := by
  exact paper_xi_chain_idempotent_comparable_finite_gcd_collapse F0 letters hchain

end Omega.Zeta
