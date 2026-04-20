import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete finite-prime-support kernel data. Both the open-surjection kernel and the
short-exact-sequence kernel are identified with the coordinate complement `T \\ S`. -/
structure PrimeSupportKernelGaloisCorrespondenceData where
  S : Finset ℕ
  T : Finset ℕ
  openKernel : Finset ℕ
  shortExactKernel : Finset ℕ
  openKernel_def : openKernel = T \ S
  shortExactKernel_def : shortExactKernel = T \ S

namespace PrimeSupportKernelGaloisCorrespondenceData

/-- The coordinate projection from `K_T` to `K_S` is encoded by disjointness of the visible and
kernel supports together with the exact support decomposition. -/
def openSurjectionWitness (D : PrimeSupportKernelGaloisCorrespondenceData) : Prop :=
  Disjoint D.S D.openKernel ∧ D.S ∪ D.openKernel = D.T

/-- The corresponding short exact sequence is encoded by the same support decomposition for the
kernel support. -/
def shortExactSequenceWitness (D : PrimeSupportKernelGaloisCorrespondenceData) : Prop :=
  Disjoint D.S D.shortExactKernel ∧ D.S ∪ D.shortExactKernel = D.T

/-- Subset detection from the open-surjection kernel decomposition. -/
def subsetIffOpenSurjection (D : PrimeSupportKernelGaloisCorrespondenceData) : Prop :=
  D.S ⊆ D.T ↔ D.openSurjectionWitness

/-- Subset detection from the short exact sequence kernel decomposition. -/
def subsetIffShortExactSequence (D : PrimeSupportKernelGaloisCorrespondenceData) : Prop :=
  D.S ⊆ D.T ↔ D.shortExactSequenceWitness

lemma diff_disjoint (S T : Finset ℕ) : Disjoint S (T \ S) := by
  refine Finset.disjoint_left.mpr ?_
  intro x hxS hxDiff
  exact (Finset.mem_sdiff.mp hxDiff).2 hxS

lemma union_diff_eq_of_subset {S T : Finset ℕ} (hST : S ⊆ T) : S ∪ (T \ S) = T := by
  ext x
  constructor
  · intro hx
    rcases Finset.mem_union.mp hx with hxS | hxDiff
    · exact hST hxS
    · exact (Finset.mem_sdiff.mp hxDiff).1
  · intro hxT
    by_cases hxS : x ∈ S
    · exact Finset.mem_union.mpr (Or.inl hxS)
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hxT, hxS⟩))

lemma subset_of_union_eq_right {S K T : Finset ℕ} (hUnion : S ∪ K = T) : S ⊆ T := by
  intro x hxS
  have hxUnion : x ∈ S ∪ K := Finset.mem_union.mpr (Or.inl hxS)
  rwa [hUnion] at hxUnion

end PrimeSupportKernelGaloisCorrespondenceData

open PrimeSupportKernelGaloisCorrespondenceData

/-- Paper-facing prime-support / kernel Galois correspondence. Identifying both kernels with the
coordinate complement `T \\ S` makes subset inclusion equivalent to either the open-surjection or
the short-exact support decomposition. -/
theorem paper_xi_time_part56ea_prime_support_kernel_galois_correspondence
    (D : PrimeSupportKernelGaloisCorrespondenceData) :
    D.subsetIffOpenSurjection ∧ D.subsetIffShortExactSequence := by
  refine ⟨?_, ?_⟩
  · constructor
    · intro hST
      refine ⟨?_, ?_⟩
      · simpa [D.openKernel_def] using diff_disjoint D.S D.T
      · simpa [D.openKernel_def] using union_diff_eq_of_subset hST
    · intro hOpen
      exact subset_of_union_eq_right hOpen.2
  · constructor
    · intro hST
      refine ⟨?_, ?_⟩
      · simpa [D.shortExactKernel_def] using diff_disjoint D.S D.T
      · simpa [D.shortExactKernel_def] using union_diff_eq_of_subset hST
    · intro hShort
      exact subset_of_union_eq_right hShort.2

end Omega.Zeta
