import Mathlib.Tactic
import Mathlib.Data.Nat.Log
import Omega.POM.MaryAuxlengthSeeds

namespace Omega.POM

/-- Exact M-ary auxiliary length criterion via ceiling logarithms.
    cor:pom-injectivization-mary-auxlength-exact -/
theorem paper_pom_injectivization_mary_auxlength_exact
    (M D L : ℕ) (hM : 2 ≤ M) :
    Nat.clog M D ≤ L ↔ D ≤ M ^ L := by
  have hM' : 1 < M := by omega
  exact Nat.clog_le_iff_le_pow hM'

end Omega.POM
