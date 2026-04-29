import Omega.Zeta.XiChainInteriorBooleanMobiusCharacteristicMaxchains

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part65d-chain-interior-boolean-arithmeticization`. The
part-65d arithmeticization is the existing Boolean-chain package under its paper-facing label. -/
theorem paper_xi_time_part65d_chain_interior_boolean_arithmeticization (n : Nat) :
    xi_chain_interior_boolean_mobius_characteristic_maxchains_package n := by
  exact paper_xi_chain_interior_boolean_mobius_characteristic_maxchains n

/-- Paper label:
`cor:xi-time-part65d-chain-interval-mobius-characteristic-arithmetic`. Boolean intervals inherit
the interval Möbius sign and binomial characteristic-polynomial arithmetic from the chain package. -/
theorem paper_xi_time_part65d_chain_interval_mobius_characteristic_arithmetic {n : ℕ}
    (I J : Finset (Fin (n + 1))) (hIJ : I ⊆ J) :
    (∀ S T : Finset (Fin ((J \ I).card)), S ⊆ T →
      Omega.Zeta.booleanIntervalSign S T = (-1 : ℤ) ^ (T.card - S.card)) ∧
      (∀ q : ℤ, (∑ S : Finset (Fin ((J \ I).card)), q ^ S.card) =
        (q + 1) ^ ((J \ I).card)) := by
  classical
  have _ : I ⊆ J := hIJ
  have h :=
    paper_xi_chain_interior_boolean_mobius_characteristic_maxchains ((J \ I).card + 1)
  dsimp [xi_chain_interior_boolean_mobius_characteristic_maxchains_package] at h
  exact ⟨by simpa using h.2.2.1, by simpa using h.2.2.2.1⟩

end Omega.Zeta
