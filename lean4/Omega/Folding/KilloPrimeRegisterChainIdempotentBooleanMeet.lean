import Omega.Folding.KilloPrimeRegisterChainIdempotentBooleanRank

namespace Omega.Folding

/-- The chain-idempotent Boolean meet corresponding to the missing coordinates of `F ∩ G`
recovers that intersection exactly.
    thm:killo-prime-register-chain-idempotent-boolean-meet -/
theorem paper_killo_prime_register_chain_idempotent_boolean_meet (n : ℕ)
    (F G : Finset (Fin (n - 1))) :
    booleanMeetOfFamily
        (Finset.univ.filter fun j : Fin (n - 1) => j ∉ (F ∩ G))
        (chainBooleanGenerator (n - 1)) = F ∩ G := by
  simpa using booleanMeetOfFamily_missing_coordinates (n - 1) (F ∩ G)

end Omega.Folding
