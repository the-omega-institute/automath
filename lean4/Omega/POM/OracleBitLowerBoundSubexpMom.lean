import Mathlib.Tactic

namespace Omega.POM

/-- Size of the blindspot block that carries the uniformly distributed light mass. -/
def blindspotBlockSize (m : ℕ) : ℕ := 2 ^ m

/-- A choice of blindspot support inside the light block. Each Boolean function encodes a subset. -/
abbrev BlindspotSupport (m : ℕ) := Fin (blindspotBlockSize m) → Bool

/-- Number of distinct blindspot support choices compatible with the fixed heavy block. -/
def blindspotOracleCount (m : ℕ) : ℕ := Fintype.card (BlindspotSupport m)

/-- Base-2 oracle bits needed to identify a single blindspot support. -/
def blindspotOracleBits (m : ℕ) : ℕ := Nat.log 2 (blindspotOracleCount m)

@[simp] theorem blindspotOracleCount_eq (m : ℕ) :
    blindspotOracleCount m = 2 ^ blindspotBlockSize m := by
  simp [blindspotOracleCount, BlindspotSupport, blindspotBlockSize]

/-- Paper-facing subexponential-moment oracle lower bound: once the heavy block is fixed, the
remaining freedom is the choice of a light support inside a block of size `2^m`, hence the
candidate family has `2^(2^m)` elements and therefore needs `2^m` bits to resolve. -/
theorem paper_pom_oracle_bit_lower_bound_subexp_mom (m : ℕ) :
    blindspotOracleBits m = blindspotBlockSize m := by
  rw [blindspotOracleBits, blindspotOracleCount_eq, Nat.log_pow (by norm_num : 1 < 2)]

end Omega.POM
