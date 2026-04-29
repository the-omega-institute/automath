import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Paper label: `cor:conclusion-tqft-sphere-partition-function-s2`.
At genus zero, the genus partition-function formula specializes to the second moment. -/
theorem paper_conclusion_tqft_sphere_partition_function_s2 {X : Type*} [Fintype X]
    (d : X → ℕ) (Z : ℕ → ℕ) (hZ : ∀ g, Z g = ∑ x, d x ^ (g + 2)) :
    Z 0 = ∑ x, d x ^ 2 := by
  simpa using hZ 0

/-- Paper label: `thm:conclusion-tqft-witten-index-susy-subtqft`. The survivor predicate
selects the finite idempotent basis, and the supplied central-idempotent, subalgebra,
uniqueness, and genus partition-function certificates assemble the SUSY sub-TQFT package. -/
theorem paper_conclusion_tqft_witten_index_susy_subtqft {X : Type*} [Fintype X]
    (survives badComponent : X → Prop) [DecidablePred survives] (d : X → Nat)
    (Zsusy : Nat → Nat) (centralIdempotent subFrobenius uniqueTQFT : Prop)
    (h_survives : ∀ x, survives x ↔ ¬ badComponent x) (hcentral : centralIdempotent)
    (hsub : subFrobenius) (hunique : uniqueTQFT)
    (hZ : ∀ g, Zsusy g = ∑ x, if survives x then d x ^ (g + 2) else 0) :
    (∀ x, survives x ↔ ¬ badComponent x) ∧ centralIdempotent ∧ subFrobenius ∧
      uniqueTQFT ∧ ∀ g, Zsusy g = ∑ x, if survives x then d x ^ (g + 2) else 0 := by
  exact ⟨h_survives, hcentral, hsub, hunique, hZ⟩

end Omega.Conclusion
