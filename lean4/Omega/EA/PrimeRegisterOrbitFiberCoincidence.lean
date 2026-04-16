import Mathlib.Logic.Relation
import Omega.EA.PrimeRegisterLocalMoves
import Omega.EA.PrimeRegisterNormalFormUniqueness

namespace Omega.EA

open Omega.Rewrite

/-- Two prime-register states lie in the same local Fibonacci orbit when they admit a common
    descendant under the value-preserving rewrite system. -/
def PrimeRegisterOrbit (r s : DigitCfg) : Prop :=
  Relation.Join (Relation.ReflTransGen Step) r s

/-- The Fibonacci-valuation fiber through a prime-register state. -/
def PrimeRegisterValueFiber (r : DigitCfg) : Set DigitCfg :=
  {s | valPr s = valPr r}

/-- Common descendants stay in the same valuation fiber. -/
private theorem primeRegisterOrbit_subset_valueFiber {r s : DigitCfg}
    (hrs : PrimeRegisterOrbit r s) : s ∈ PrimeRegisterValueFiber r := by
  rcases hrs with ⟨t, hrt, hst⟩
  have hrtVal : valPr t = valPr r := by
    simpa [valPr, Rewrite.value, Rewrite.weighted, Rewrite.digitWeight] using reflTransGen_value hrt
  have hstVal : valPr t = valPr s := by
    simpa [valPr, Rewrite.value, Rewrite.weighted, Rewrite.digitWeight] using reflTransGen_value hst
  exact hstVal.symm.trans hrtVal

/-- Equal prime-register valuations force the same local Fibonacci orbit by transport through the
    canonical normal form. -/
private theorem valueFiber_subset_primeRegisterOrbit {r s : DigitCfg}
    (hrs : s ∈ PrimeRegisterValueFiber r) : PrimeRegisterOrbit r s := by
  have hrNF : Relation.ReflTransGen Step r (NF_pr r) :=
    (paper_prime_register_normal_form_uniqueness r).1
  have hsNF : Relation.ReflTransGen Step s (NF_pr s) :=
    (paper_prime_register_normal_form_uniqueness s).1
  have hNF : NF_pr s = NF_pr r := by
    exact congrArg R_F hrs
  refine ⟨NF_pr r, hrNF, ?_⟩
  simpa [hNF] using hsNF

/-- Paper-facing wrapper: the local Fibonacci-move orbit of a prime-register state is exactly its
    Fibonacci-valuation fiber.
    thm:prime-register-orbit-fiber-coincidence -/
theorem paper_prime_register_orbit_fiber_coincidence (r s : DigitCfg) :
    PrimeRegisterOrbit r s ↔ s ∈ PrimeRegisterValueFiber r := by
  constructor
  · exact primeRegisterOrbit_subset_valueFiber
  · exact valueFiber_subset_primeRegisterOrbit

end Omega.EA
