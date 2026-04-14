import Mathlib.Tactic
import Omega.EA.PrimeRegisterFibValuation

namespace Omega.EA.InternalProductAddsValues

open Omega.EA

/-- Prime register valuation is additive and vanishes at zero.
    prop:prime-register-internal-product-adds-values -/
theorem paper_prime_register_internal_product_adds_values :
    (∀ (a b : ℕ →₀ ℕ), valPr (a + b) = valPr a + valPr b) ∧
    valPr 0 = 0 :=
  ⟨valPr_add, valPr_zero⟩

end Omega.EA.InternalProductAddsValues
