import Mathlib

namespace Omega.POM

open scoped BigOperators

/-- The distinct Fibonacci-cube factor lengths appearing in the Cartesian decomposition. -/
def FiberReconstructionLengthClass (lengths : List ℕ) :=
  {ℓ // ℓ ∈ lengths.eraseDups.toFinset}

instance fiberReconstructionLengthClassDecidableEq (lengths : List ℕ) :
    DecidableEq (FiberReconstructionLengthClass lengths) := by
  classical
  unfold FiberReconstructionLengthClass
  infer_instance

noncomputable instance fiberReconstructionLengthClassFintype (lengths : List ℕ) :
    Fintype (FiberReconstructionLengthClass lengths) := by
  classical
  unfold FiberReconstructionLengthClass
  infer_instance

/-- Each Cartesian prime factor carries the order-two reversal automorphism from the Fibonacci
cube antipode. -/
abbrev FiberwiseReversalFactor (lengths : List ℕ) :=
  Fin lengths.length → ZMod 2

/-- Same-length Cartesian prime factors may be permuted independently inside each length block. -/
abbrev SameLengthFactorPermutations (lengths : List ℕ) :=
  (ℓ : FiberReconstructionLengthClass lengths) → Equiv.Perm (Fin (lengths.count ℓ.1))

noncomputable instance sameLengthFactorPermutationsFintype (lengths : List ℕ) :
    Fintype (SameLengthFactorPermutations lengths) := by
  classical
  unfold SameLengthFactorPermutations
  infer_instance

/-- Canonical finite proxy for the fiber-reconstruction automorphism package: factorwise reversal
choices together with permutations of equal-length Cartesian prime factors. -/
def FiberReconstructionAutModel (lengths : List ℕ) :=
  FiberwiseReversalFactor lengths × SameLengthFactorPermutations lengths

noncomputable instance fiberReconstructionAutModelFintype (lengths : List ℕ) :
    Fintype (FiberReconstructionAutModel lengths) := by
  classical
  unfold FiberReconstructionAutModel
  infer_instance

private theorem fiberwiseReversalFactor_card (lengths : List ℕ) :
    Fintype.card (FiberwiseReversalFactor lengths) = 2 ^ lengths.length := by
  simpa [FiberwiseReversalFactor] using
    (Fintype.card_fun : Fintype.card (Fin lengths.length → ZMod 2) =
      Fintype.card (ZMod 2) ^ Fintype.card (Fin lengths.length))

private theorem sameLengthFactorPermutations_card (lengths : List ℕ) :
    Fintype.card (SameLengthFactorPermutations lengths) =
      Finset.prod (lengths.eraseDups.toFinset) fun ℓ => Nat.factorial (lengths.count ℓ) := by
  classical
  calc
    Fintype.card (SameLengthFactorPermutations lengths)
        = ∏ ℓ : FiberReconstructionLengthClass lengths,
            Fintype.card (Equiv.Perm (Fin (lengths.count ℓ.1))) := by
              simpa [SameLengthFactorPermutations] using
                (Fintype.card_pi : Fintype.card ((ℓ : FiberReconstructionLengthClass lengths) →
                  Equiv.Perm (Fin (lengths.count ℓ.1))) = _)
    _ = ∏ ℓ : FiberReconstructionLengthClass lengths, Nat.factorial (lengths.count ℓ.1) := by
          simp [Fintype.card_perm]
    _ = Finset.prod (lengths.eraseDups.toFinset) fun ℓ => Nat.factorial (lengths.count ℓ) := by
          simpa [FiberReconstructionLengthClass] using
            (Finset.prod_coe_sort (s := lengths.eraseDups.toFinset)
              (f := fun ℓ => Nat.factorial (lengths.count ℓ)))

/-- Paper-facing automorphism package for the Cartesian prime-factor reconstruction graph:
each factor contributes its `Z/2Z` reversal, same-length factors may be permuted, and the
resulting finite proxy has cardinality `2^r * ∏_ℓ m_ℓ!`.
    thm:pom-fiber-reconstruction-aut-group -/
theorem paper_pom_fiber_reconstruction_aut_group (lengths : List ℕ) :
    Nonempty (FiberReconstructionAutModel lengths ≃
      FiberwiseReversalFactor lengths × SameLengthFactorPermutations lengths) ∧
      Fintype.card (FiberwiseReversalFactor lengths) = 2 ^ lengths.length ∧
      Fintype.card (SameLengthFactorPermutations lengths) =
        (Finset.prod (lengths.eraseDups.toFinset) fun ℓ => Nat.factorial (lengths.count ℓ)) ∧
      Fintype.card (FiberReconstructionAutModel lengths) =
        2 ^ lengths.length *
          (Finset.prod (lengths.eraseDups.toFinset) fun ℓ => Nat.factorial (lengths.count ℓ)) := by
  classical
  have hReversal := fiberwiseReversalFactor_card lengths
  have hPermutations := sameLengthFactorPermutations_card lengths
  refine ⟨⟨Equiv.refl _⟩, hReversal, hPermutations, ?_⟩
  calc
    Fintype.card (FiberReconstructionAutModel lengths)
        = Fintype.card (FiberwiseReversalFactor lengths) *
            Fintype.card (SameLengthFactorPermutations lengths) := by
              simpa [FiberReconstructionAutModel] using
                (Fintype.card_prod (FiberwiseReversalFactor lengths)
                  (SameLengthFactorPermutations lengths))
    _ = 2 ^ lengths.length *
          (Finset.prod (lengths.eraseDups.toFinset) fun ℓ => Nat.factorial (lengths.count ℓ)) := by
          rw [hReversal, hPermutations]

end Omega.POM
