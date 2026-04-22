import Omega.Core.WalshStokes

namespace Omega.Discussion

/-- Paper-facing discussion wrapper for the higher-order Walsh--Stokes flux formula.
    thm:discussion-walsh-stokes-higher-flux -/
theorem paper_discussion_walsh_stokes_higher_flux
    (n : Nat) (A : Finset (Fin n)) (f : Omega.Word n → ℤ) :
    Omega.Core.walshFlux A f =
      ∑ w : Omega.Word n, (-1 : ℤ) ^ ((A.filter fun i => w i = true).card) * f w := by
  simpa using Omega.Core.walshStokes_finset (n := n) A f

end Omega.Discussion
