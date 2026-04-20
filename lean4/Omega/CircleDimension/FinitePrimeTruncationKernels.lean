import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Tactic
import Omega.CircleDimension.SolenoidKernelProductZp

namespace Omega.CircleDimension

/-- Prime axes added when enlarging the finite localization support from `S` to `S'`. -/
abbrev AddedPrimeSupport (S S' : Finset ℕ) :=
  {p : ℕ // p ∈ S' ∧ p.Prime ∧ p ∉ S}

instance instFactAddedPrimeSupportPrime {S S' : Finset ℕ} (p : AddedPrimeSupport S S') :
    Fact p.1.Prime :=
  ⟨p.2.2.1⟩

/-- Product of `p`-adic axes indexed by the added primes `S' \ S`. -/
abbrev AddedPrimeProduct (S S' : Finset ℕ) :=
  ∀ p : AddedPrimeSupport S S', ℤ_[p.1]

/-- All prime axes of the full rational dual. -/
abbrev AllPrimeSupport := {p : ℕ // p.Prime}

instance instFactAllPrimeSupportPrime (p : AllPrimeSupport) : Fact p.1.Prime :=
  ⟨p.2⟩

/-- Product of all `p`-adic axes. -/
abbrev AllPrimeProduct :=
  ∀ p : AllPrimeSupport, ℤ_[p.1]

/-- Prime axes omitted by the finite localization support `S`. -/
abbrev ComplementPrimeSupport (S : Finset ℕ) :=
  {p : ℕ // p.Prime ∧ p ∉ S}

instance instFactComplementPrimeSupportPrime {S : Finset ℕ} (p : ComplementPrimeSupport S) :
    Fact p.1.Prime :=
  ⟨p.2.1⟩

/-- Product of `p`-adic axes indexed by the primes outside `S`. -/
abbrev ComplementPrimeProduct (S : Finset ℕ) :=
  ∀ p : ComplementPrimeSupport S, ℤ_[p.1]

/-- Restriction from the larger finite-prime truncation `S'` to the smaller truncation `S`. -/
def finitePrimeTruncationMap {S S' : Finset ℕ} (hSS' : S ⊆ S') :
    SolenoidKernelProductZpModel S' → SolenoidKernelProductZpModel S :=
  fun x p => x ⟨p.1, And.intro (hSS' p.2.1) p.2.2⟩

/-- Kernel of the finite-prime truncation map `Σ_{S'} ↠ Σ_S`. -/
abbrev FinitePrimeTruncationKernel {S S' : Finset ℕ} (hSS' : S ⊆ S') :=
  {x : SolenoidKernelProductZpModel S' // finitePrimeTruncationMap hSS' x = 0}

/-- Restriction from the full rational dual to the finite localization support `S`. -/
def universalPrimeTruncationMap (S : Finset ℕ) :
    AllPrimeProduct → SolenoidKernelProductZpModel S :=
  fun x p => x ⟨p.1, p.2.2⟩

/-- Kernel of the universal truncation map `Σ_ℚ ↠ Σ_S`. -/
abbrev UniversalPrimeTruncationKernel (S : Finset ℕ) :=
  {x : AllPrimeProduct // universalPrimeTruncationMap S x = 0}

theorem finitePrimeTruncationMap_surjective {S S' : Finset ℕ} (hSS' : S ⊆ S') :
    Function.Surjective (finitePrimeTruncationMap hSS') := by
  intro x
  refine ⟨fun p => if hp : p.1 ∈ S then x ⟨p.1, And.intro hp p.2.2⟩ else 0, ?_⟩
  ext p
  simp [finitePrimeTruncationMap, p.2.1]

theorem universalPrimeTruncationMap_surjective (S : Finset ℕ) :
    Function.Surjective (universalPrimeTruncationMap S) := by
  intro x
  refine ⟨fun p => if hp : p.1 ∈ S then x ⟨p.1, And.intro hp p.2⟩ else 0, ?_⟩
  ext p
  simp [universalPrimeTruncationMap, p.2.1]

/-- The kernel of `Σ_{S'} ↠ Σ_S` is exactly the product of the added `p`-adic axes. -/
noncomputable def finitePrimeTruncationKernelEquivAddedPrimeProduct {S S' : Finset ℕ}
    (hSS' : S ⊆ S') :
    FinitePrimeTruncationKernel hSS' ≃ AddedPrimeProduct S S' where
  toFun x p := x.1 ⟨p.1, And.intro p.2.1 p.2.2.1⟩
  invFun y :=
    ⟨fun p => if hp : p.1 ∈ S then 0 else y ⟨p.1, And.intro p.2.1 (And.intro p.2.2 hp)⟩, by
      ext p
      simp [finitePrimeTruncationMap, p.2.1]⟩
  left_inv x := by
    apply Subtype.ext
    ext p
    by_cases hp : p.1 ∈ S
    · have hp' : (⟨p.1, And.intro (hSS' hp) p.2.2⟩ : SolenoidPrimeSupport S') = p := by
        ext
        rfl
      have hzero : x.1 p = 0 := by
        have hx := congrFun x.2 ⟨p.1, And.intro hp p.2.2⟩
        simpa [finitePrimeTruncationMap, hp'] using hx
      simp [hp, hzero]
    · simp [hp]
  right_inv y := by
    ext p
    simp [p.2.2.2]

/-- The kernel of `Σ_ℚ ↠ Σ_S` is exactly the product of the `p`-adic axes outside `S`. -/
noncomputable def universalPrimeTruncationKernelEquivComplement (S : Finset ℕ) :
    UniversalPrimeTruncationKernel S ≃ ComplementPrimeProduct S where
  toFun x p := x.1 ⟨p.1, p.2.1⟩
  invFun y :=
    ⟨fun p => if hp : p.1 ∈ S then 0 else y ⟨p.1, And.intro p.2 hp⟩, by
      ext p
      simp [universalPrimeTruncationMap, p.2.1]⟩
  left_inv x := by
    apply Subtype.ext
    ext p
    by_cases hp : p.1 ∈ S
    · have hp' : (⟨p.1, p.2⟩ : AllPrimeSupport) = p := by
        ext
        rfl
      have hzero : x.1 p = 0 := by
        have hx := congrFun x.2 ⟨p.1, And.intro hp p.2⟩
        simpa [universalPrimeTruncationMap, hp'] using hx
      simp [hp, hzero]
    · simp [hp]
  right_inv y := by
    ext p
    simp [p.2.2]

/-- Paper-facing kernel description for finite prime truncations: restriction from the larger
finite support and from the full rational dual are both surjective, and their kernels are the
products of the newly added or omitted `p`-adic axes. -/
theorem paper_cdim_star_finite_prime_truncation_kernels {S S' : Finset ℕ} (hSS' : S ⊆ S') :
    Function.Surjective (finitePrimeTruncationMap hSS') ∧
      Nonempty (FinitePrimeTruncationKernel hSS' ≃ AddedPrimeProduct S S') ∧
      Function.Surjective (universalPrimeTruncationMap S) ∧
      Nonempty (UniversalPrimeTruncationKernel S ≃ ComplementPrimeProduct S) := by
  exact ⟨finitePrimeTruncationMap_surjective hSS',
    ⟨finitePrimeTruncationKernelEquivAddedPrimeProduct hSS'⟩,
    universalPrimeTruncationMap_surjective S,
    ⟨universalPrimeTruncationKernelEquivComplement S⟩⟩

end Omega.CircleDimension
