import Omega.GroupUnification.GroupJGPrimeRegisterInitialObject

namespace Omega.Zeta

/-- Concrete data for the target Gödel-shift encoder. -/
structure xi_godel_prime_register_initial_object_data where
  Carrier : Type
  instAddCommMonoid : AddCommMonoid Carrier
  shift : Carrier →+ Carrier
  seed : Carrier

attribute [instance] xi_godel_prime_register_initial_object_data.instAddCommMonoid

namespace xi_godel_prime_register_initial_object_data

/-- View the target encoder as the existing Gödel-shift encoder structure. -/
def asGShiftEncoder (D : xi_godel_prime_register_initial_object_data) :
    Omega.GroupUnification.GShiftEncoder where
  Carrier := D.Carrier
  instAddCommMonoid := D.instAddCommMonoid
  shift := D.shift
  seed := D.seed

/-- Objecthood of the concrete prime register follows from injectivity of its standard basis map. -/
def isPrimeRegisterObject (_D : xi_godel_prime_register_initial_object_data) : Prop :=
  Function.Injective Omega.GroupUnification.primeRegisterSequenceEncoder

/-- Initiality against the target shift-compatible encoder. -/
def isInitial (D : xi_godel_prime_register_initial_object_data) : Prop :=
  Omega.GroupUnification.PrimeRegisterInitialFor D.asGShiftEncoder

end xi_godel_prime_register_initial_object_data

/-- Paper label: `thm:xi-godel-prime-register-initial-object`. -/
theorem paper_xi_godel_prime_register_initial_object
    (D : xi_godel_prime_register_initial_object_data) :
    D.isPrimeRegisterObject ∧ D.isInitial := by
  exact ⟨Omega.GroupUnification.primeRegisterSequenceEncoder_injective,
    Omega.GroupUnification.paper_group_jg_prime_register_initial_object D.asGShiftEncoder⟩

end Omega.Zeta
