import Mathlib.Tactic

namespace Omega.Conclusion

/-- Bit vectors of length `q`. -/
abbrev BitVec (q : ℕ) := Fin q → Bool

/-- Coordinate permutation action on bit vectors. -/
def permuteBitVec {q : ℕ} (σ : Equiv.Perm (Fin q)) (u : BitVec q) : BitVec q :=
  u ∘ σ

/-- Entrywise model of `J^{⊗ q}`. -/
def allOnesKroneckerEntry (q : ℕ) (_u _v : BitVec q) : ℚ :=
  1

/-- Entrywise model of `K^{⊗ q}`: the entry is `1` exactly when no coordinate is simultaneously
`1` in both words. -/
def softcoreKroneckerEntry (q : ℕ) (u v : BitVec q) : ℚ :=
  if ∀ i, u i = false ∨ v i = false then 1 else 0

/-- Entrywise model of the softcore kernel `T^(q)`. -/
def softcoreKernelEntry (q : ℕ) (u v : BitVec q) : ℚ :=
  (1 / 2 : ℚ) * (1 + if ∀ i, u i = false ∨ v i = false then 1 else 0)

/-- A kernel commutes with coordinate permutations when its entries are unchanged by permuting the
coordinates in both arguments simultaneously. This is the finite-entry version of restricting to
the symmetric subspace. -/
def CommutesWithCoordinatePermutations {q : ℕ} (A : BitVec q → BitVec q → ℚ) : Prop :=
  ∀ σ u v, A (permuteBitVec σ u) (permuteBitVec σ v) = A u v

/-- Paper-facing softcore Kronecker/symmetric-power decomposition.
    thm:conclusion-softcore-kronecker-sympower-decomposition -/
theorem paper_conclusion_softcore_kronecker_sympower_decomposition (q : ℕ) :
    (∀ u v,
      softcoreKernelEntry q u v =
        (1 / 2 : ℚ) * (allOnesKroneckerEntry q u v + softcoreKroneckerEntry q u v)) ∧
      CommutesWithCoordinatePermutations (allOnesKroneckerEntry q) ∧
      CommutesWithCoordinatePermutations (softcoreKroneckerEntry q) ∧
      CommutesWithCoordinatePermutations (softcoreKernelEntry q) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u v
    simp [softcoreKernelEntry, allOnesKroneckerEntry, softcoreKroneckerEntry]
  · intro σ u v
    simp [allOnesKroneckerEntry]
  · intro σ u v
    have hperm :
        (∀ i, (permuteBitVec σ u) i = false ∨ (permuteBitVec σ v) i = false) ↔
          ∀ i, u i = false ∨ v i = false := by
      constructor
      · intro h i
        simpa [permuteBitVec] using h (σ⁻¹ i)
      · intro h i
        simpa [permuteBitVec] using h (σ i)
    by_cases hleft : ∀ i, (permuteBitVec σ u) i = false ∨ (permuteBitVec σ v) i = false
    · have hright : ∀ i, u i = false ∨ v i = false := hperm.mp hleft
      simp [softcoreKroneckerEntry, hleft, hright]
    · have hright : ¬ ∀ i, u i = false ∨ v i = false := by
        intro h
        exact hleft (hperm.mpr h)
      simp [softcoreKroneckerEntry, hleft, hright]
  · intro σ u v
    have hperm :
        (∀ i, (permuteBitVec σ u) i = false ∨ (permuteBitVec σ v) i = false) ↔
          ∀ i, u i = false ∨ v i = false := by
      constructor
      · intro h i
        simpa [permuteBitVec] using h (σ⁻¹ i)
      · intro h i
        simpa [permuteBitVec] using h (σ i)
    by_cases hleft : ∀ i, (permuteBitVec σ u) i = false ∨ (permuteBitVec σ v) i = false
    · have hright : ∀ i, u i = false ∨ v i = false := hperm.mp hleft
      simp [softcoreKernelEntry, hleft, hright]
    · have hright : ¬ ∀ i, u i = false ∨ v i = false := by
        intro h
        exact hleft (hperm.mpr h)
      simp [softcoreKernelEntry, hleft, hright]

end Omega.Conclusion
