import Omega.Folding.KilloChainInteriorGodelGcdLcm
import Omega.Zeta.XiChainInteriorBooleanMobiusCharacteristicMaxchains

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-chain-interior-mobius-arithmetic-identification`.
The conclusion combines the Boolean Möbius package for chain interiors with the squarefree
Gödel `gcd`/`lcm` coding theorem. -/
theorem paper_conclusion_chain_interior_mobius_arithmetic_identification (n : ℕ) :
    Omega.Zeta.xi_chain_interior_boolean_mobius_characteristic_maxchains_package n ∧
      Omega.Folding.ChainInteriorGodelGcdLcm n := by
  exact ⟨Omega.Zeta.paper_xi_chain_interior_boolean_mobius_characteristic_maxchains n,
    Omega.Folding.paper_killo_chain_interior_godel_gcd_lcm n⟩

end Omega.Conclusion
