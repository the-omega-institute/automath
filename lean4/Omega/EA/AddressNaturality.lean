import Omega.Folding.FiberRing

namespace Omega.EA.AddressNaturality

open Omega

noncomputable section

/-- The stable address at resolution `m`, obtained by transporting an integer residue through the
ring equivalence `X m ≃+* ZMod (fib (m + 2))`. -/
noncomputable def addr (m : ℕ) (z : ℤ) : X m :=
  (X.stableValueRingEquiv m).symm (z : ZMod (Nat.fib (m + 2)))

theorem addr_add (m : ℕ) (z z' : ℤ) :
    addr m (z + z') = addr m z + addr m z' := by
  apply (X.stableValueRingEquiv m).injective
  simp [addr]

theorem addr_mul (m : ℕ) (z z' : ℤ) :
    addr m (z * z') = addr m z * addr m z' := by
  apply (X.stableValueRingEquiv m).injective
  simp [addr]

/-- Paper-facing seeds package for address naturality under stable addition and multiplication. -/
theorem paper_ea_address_naturality_seeds (m : ℕ) (z z' : ℤ) :
    addr m (z + z') = addr m z + addr m z' ∧
    addr m (z * z') = addr m z * addr m z' := by
  exact ⟨addr_add m z z', addr_mul m z z'⟩

/-- Wrapper theorem matching the paper-facing package name. -/
theorem paper_ea_address_naturality_package (m : ℕ) (z z' : ℤ) :
    addr m (z + z') = addr m z + addr m z' ∧
    addr m (z * z') = addr m z * addr m z' :=
  paper_ea_address_naturality_seeds m z z'

end

end Omega.EA.AddressNaturality
