import Mathlib.Data.Set.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

open Classical

/-- The diagonal prime-axis kernel: only the matching prime coordinate survives. -/
noncomputable def primeAdicAxisKernel (p q : ℕ) : ℤ :=
  if p = q then 1 else 0

/-- Restrict the diagonal kernel to the declared source and target prime supports. -/
noncomputable def primeAdicSeparatedKernel (S T : Set ℕ) (p q : ℕ) : ℤ :=
  if p ∈ S ∧ q ∈ T then primeAdicAxisKernel p q else 0

/-- The `q`-th target coordinate only reads the `q`-th source coordinate. -/
noncomputable def primeAdicAxisCoordinateMap (S T : Set ℕ) (x : ℕ → ℤ) (q : ℕ) : ℤ :=
  primeAdicSeparatedKernel S T q q * x q

/-- Every target prime coordinate depends on finitely many source coordinates. -/
def primeAdicAxisFiniteDependence (S T : Set ℕ) : Prop :=
  ∀ q : ℕ, ∃ F : Finset ℕ, ∀ x y : ℕ → ℤ,
    (∀ p ∈ F, x p = y p) →
      primeAdicAxisCoordinateMap S T x q = primeAdicAxisCoordinateMap S T y q

/-- Off-diagonal prime blocks vanish: pro-`p` information cannot alias into a distinct pro-`q`
direction. -/
def primeAdicAxisOffDiagonalVanishing (S T : Set ℕ) : Prop :=
  ∀ p q : ℕ, p ∈ S → q ∈ T → p ≠ q → primeAdicSeparatedKernel S T p q = 0

/-- Equality of prime supports induces the tautological prime-axis isomorphism. -/
def primeAdicAxisIsomorphismRigidity (S T : Set ℕ) : Prop :=
  S = T → Nonempty ({p // p ∈ S} ≃ {q // q ∈ T})

/-- Inclusion of prime supports induces an injective map of prime axes. -/
def primeAdicAxisInjectionRigidity (S T : Set ℕ) : Prop :=
  ∀ hST : S ⊆ T, Function.Injective (fun x : {p // p ∈ S} => (⟨x.1, hST x.2⟩ : {q // q ∈ T}))

/-- Chapter-local package for the no-aliasing rigidity of prime-adic axes. Each target coordinate
depends on a single source coordinate, different prime directions do not mix, equality of prime
supports gives an isomorphism, and inclusion gives an injection on prime axes. -/
def PrimeAdicAxisNoAliasingRigidity (S T : Set Nat) : Prop :=
  primeAdicAxisFiniteDependence S T ∧
    primeAdicAxisOffDiagonalVanishing S T ∧
    primeAdicAxisIsomorphismRigidity S T ∧
    primeAdicAxisInjectionRigidity S T

/-- Paper label: `thm:conclusion-prime-adic-axis-no-aliasing-rigidity`. -/
theorem paper_conclusion_prime_adic_axis_no_aliasing_rigidity
    (S T : Set Nat) : PrimeAdicAxisNoAliasingRigidity S T := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro q
    refine ⟨{q}, ?_⟩
    intro x y hxy
    have hq : x q = y q := hxy q (by simp)
    simp [primeAdicAxisCoordinateMap, hq]
  · intro p q hp hq hpq
    simp [primeAdicSeparatedKernel, hp, hq, primeAdicAxisKernel, hpq]
  · intro hST
    subst hST
    exact ⟨Equiv.refl _⟩
  · intro hST x y hxy
    have hval :
        (⟨x.1, hST x.2⟩ : {q // q ∈ T}).1 = (⟨y.1, hST y.2⟩ : {q // q ∈ T}).1 := by
      exact congrArg (fun z : {q // q ∈ T} => z.1) hxy
    exact Subtype.ext hval

end Omega.Conclusion
