import Mathlib.Data.Nat.Factorization.Basic
import Omega.EA.PrimeRegisterOrbitFiberCoincidence

namespace Omega.EA

/-- The external ledger records the prime-factor ledger of the Fibonacci valuation. -/
noncomputable def externalLedger (r : DigitCfg) : ℕ →₀ ℕ :=
  (valPr r).factorization

/-- The external ledger is constant on prime-register local-move orbits, hence in particular on
the orbit through the canonical normal form. `prop:prime-register-external-ledger-orbit-invariance`
-/
theorem paper_prime_register_external_ledger_orbit_invariance
    (r s : DigitCfg) (hrs : PrimeRegisterOrbit r s) (_hval : 1 ≤ valPr r) :
    externalLedger r = externalLedger s ∧
      externalLedger r = externalLedger (NF_pr r) := by
  have hs : valPr s = valPr r :=
    (paper_prime_register_orbit_fiber_coincidence r s).1 hrs
  refine ⟨?_, ?_⟩
  · simp [externalLedger, hs]
  · simp [externalLedger, NF_pr]

end Omega.EA
