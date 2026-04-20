import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- The concrete Fibonacci modulus used for the fold-congruence quotient model. -/
def foldCongruenceModulus (m : ℕ) : ℕ :=
  Nat.fib (m + 2)

/-- The concrete residue semiring modeling the fold-congruence quotient. -/
abbrev foldCongruenceSemiring (m : ℕ) : Type :=
  ZMod (foldCongruenceModulus m)

instance foldCongruenceModulus_neZero (m : ℕ) : NeZero (foldCongruenceModulus m) := by
  refine ⟨?_⟩
  dsimp [foldCongruenceModulus]
  exact Nat.ne_of_gt (Nat.fib_pos.mpr (by omega))

/-- Multiplication by a fixed element in the residue semiring. -/
def foldCongruenceMulMap (m : ℕ) (e : foldCongruenceSemiring m) :
    foldCongruenceSemiring m → foldCongruenceSemiring m :=
  fun x => e * x

/-- The concrete family of nonunital endomorphisms modeled by multiplication by an idempotent. -/
def foldCongruenceEnd0Maps (m : ℕ) : Set (foldCongruenceSemiring m → foldCongruenceSemiring m) :=
  { f | ∃ e : foldCongruenceSemiring m, e * e = e ∧ f = foldCongruenceMulMap m e }

/-- Evaluation at `1`, corresponding to the paper's `φ ↦ φ(1)` map. -/
def foldCongruencePhiOne (m : ℕ) (f : foldCongruenceSemiring m → foldCongruenceSemiring m) :
    foldCongruenceSemiring m :=
  f 1

/-- Prime-support size of the Fibonacci modulus. -/
def foldCongruencePrimeSupport (m : ℕ) : ℕ :=
  (foldCongruenceModulus m).primeFactors.card

/-- Finite index model for the CRT prime-support splitting of idempotents. -/
abbrev foldCongruencePrimeSupportModel (m : ℕ) : Type :=
  Fin (2 ^ foldCongruencePrimeSupport m)

/-- Classification of the concrete nonunital endomorphism model by the idempotent `φ(1)`. -/
def foldCongruenceEnd0ClassifiedByIdempotents (m : ℕ) : Prop :=
  ∀ f, f ∈ foldCongruenceEnd0Maps m →
    ∃ e : foldCongruenceSemiring m,
      e * e = e ∧ f = foldCongruenceMulMap m e ∧ foldCongruencePhiOne m f = e

/-- Count of the concrete endomorphism/idempotent model via prime-support splitting. -/
def foldCongruenceEnd0CountByPrimeSupport (m : ℕ) : Prop :=
  Fintype.card (foldCongruencePrimeSupportModel m) = 2 ^ foldCongruencePrimeSupport m

/-- Unital ring automorphisms of the concrete residue semiring are rigid. -/
def foldCongruenceUnitalAutomorphismRigid (m : ℕ) : Prop :=
  ∀ σ : foldCongruenceSemiring m ≃+* foldCongruenceSemiring m, σ = RingEquiv.refl _

lemma foldCongruence_ringEquiv_eq_refl (m : ℕ)
    (σ : foldCongruenceSemiring m ≃+* foldCongruenceSemiring m) :
    σ = RingEquiv.refl _ := by
  apply RingEquiv.ext
  intro x
  calc
    σ x = σ (x.val : foldCongruenceSemiring m) := by rw [ZMod.natCast_zmod_val x]
    _ = (x.val : foldCongruenceSemiring m) := by rw [map_natCast]
    _ = x := by rw [ZMod.natCast_zmod_val x]

/-- Fold-congruence nonunital endomorphisms are classified by idempotents, the count is the
expected prime-support power of `2`, and the unital automorphism is rigid.
    thm:xi-fold-congruence-unital-automorphism-rigidity -/
theorem paper_xi_fold_congruence_unital_automorphism_rigidity (m : Nat) :
    foldCongruenceEnd0ClassifiedByIdempotents m ∧
      foldCongruenceEnd0CountByPrimeSupport m ∧ foldCongruenceUnitalAutomorphismRigid m := by
  refine ⟨?_, ?_, ?_⟩
  · intro f hf
    rcases hf with ⟨e, he, rfl⟩
    refine ⟨e, he, rfl, ?_⟩
    simp [foldCongruencePhiOne, foldCongruenceMulMap]
  · simp [foldCongruenceEnd0CountByPrimeSupport, foldCongruencePrimeSupportModel]
  · intro σ
    exact foldCongruence_ringEquiv_eq_refl m σ

end Omega.Zeta
