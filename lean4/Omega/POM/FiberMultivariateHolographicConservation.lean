import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

/-- Binary words on `m` coordinates. -/
abbrev FiberBinaryWord (m : ℕ) := Fin m → Bool

/-- The support set of a binary word. This is the canonical fiber-to-subset parametrization used
for the multivariate cube expansion. -/
def fiberBinaryWordSupport {m : ℕ} (ω : FiberBinaryWord m) : Finset (Fin m) :=
  Finset.univ.filter fun i => ω i

/-- The monomial attached to one binary word. -/
def fiberBinaryWordMonomial {α : Type*} [CommSemiring α] {m : ℕ}
    (z : Fin m → α) (ω : FiberBinaryWord m) : α :=
  Finset.prod Finset.univ fun i : Fin m => if ω i then z i else 1

/-- The monomial attached to one fiber support set. -/
def fiberSupportMonomial {α : Type*} [CommSemiring α] {m : ℕ}
    (z : Fin m → α) (S : Finset (Fin m)) : α :=
  Finset.prod S z

/-- Summing the support monomials over the full support partition of the Boolean cube. -/
def sumOverFibers {α : Type*} [CommSemiring α] {m : ℕ} (z : Fin m → α) : α :=
  Finset.sum ((Finset.univ : Finset (Fin m)).powerset) (fiberSupportMonomial z)

/-- The multivariate Boolean-cube product. -/
def booleanCubeProduct {α : Type*} [CommSemiring α] {m : ℕ} (z : Fin m → α) : α :=
  Finset.prod Finset.univ fun i : Fin m => 1 + z i

/-- Each fiber support monomial matches the corresponding binary-word monomial. -/
theorem fiber_support_monomial_eq_binary_word_monomial {α : Type*} [CommSemiring α] {m : ℕ}
    (z : Fin m → α) (ω : FiberBinaryWord m) :
    fiberSupportMonomial z (fiberBinaryWordSupport ω) = fiberBinaryWordMonomial z ω := by
  simpa [fiberSupportMonomial, fiberBinaryWordSupport, fiberBinaryWordMonomial] using
    (Finset.prod_filter (s := (Finset.univ : Finset (Fin m))) (f := fun i => z i)
      (p := fun i => ω i))

/-- The support-partition sum recovers the full Boolean-cube product.
    thm:pom-fiber-multivariate-holographic-conservation -/
theorem paper_pom_fiber_multivariate_holographic_conservation
    {α : Type*} [CommSemiring α] (m : ℕ) (z : Fin m → α) :
    sumOverFibers z = booleanCubeProduct z := by
  unfold sumOverFibers booleanCubeProduct fiberSupportMonomial
  symm
  simpa [add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using
    (Finset.prod_add (f := fun i : Fin m => z i) (g := fun _ : Fin m => 1)
      (s := (Finset.univ : Finset (Fin m))))

end Omega.POM
