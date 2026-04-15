import Omega.GU.CongruenceM6IdempotentsFour

namespace Omega.GU

/-- Paper-facing registration wrapper for the four idempotents of `ZMod 21`.
    prop:congruence-m6-idempotents-four -/
theorem paper_congruence_m6_idempotents_four_registered_seeds :
    Omega.GU.CongruenceM6IdempotentsFour.idem21.card = 4 :=
  Omega.GU.CongruenceM6IdempotentsFour.paper_congruence_m6_idempotents_four_seeds

end Omega.GU
