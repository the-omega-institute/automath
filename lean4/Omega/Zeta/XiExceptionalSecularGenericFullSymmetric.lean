import Omega.Zeta.XiSecularFamilyFullSymmetricGalois

namespace Omega.Zeta

/-- Specializing the generic secular-family theorem to the exceptional-weight setting yields the
same factorial Galois-order conclusion.
    cor:xi-exceptional-secular-generic-full-symmetric -/
theorem paper_xi_exceptional_secular_generic_full_symmetric (q : Nat) (_hq : 2 ≤ q) :
    xiSecularGenericGaloisOrder q = Nat.factorial (q + 1) := by
  simpa using (paper_xi_secular_family_full_symmetric_galois q).2.2

end Omega.Zeta
