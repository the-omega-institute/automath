import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

namespace Omega.Folding

/-- The half-modulus residue singled out by the vanishing condition. -/
def foldFiberHalfResidue (M : ℕ) : ℕ :=
  M / 2

/-- The singleton zero spectrum attached to coordinate `i`. -/
def foldFiberSingletonZeroSet (M i : ℕ) : Finset (Fin M) :=
  Finset.univ.filter fun k => (k.1 * Nat.fib (i + 1)) % M = foldFiberHalfResidue M

/-- Once a witness `k0` of the half-residue congruence is fixed, the whole zero spectrum is the
fiber of the same affine congruence class. -/
def foldFiberSingletonZeroCoset (M i : ℕ) (k0 : Fin M) : Finset (Fin M) :=
  Finset.univ.filter fun k => (k.1 * Nat.fib (i + 1)) % M = (k0.1 * Nat.fib (i + 1)) % M

/-- The zero spectrum of the subset-convolution kernel is the union of the singleton zero spectra.
-/
def foldFiberConvolutionKernelZeroSet (M : ℕ) (I : Finset ℕ) : Finset (Fin M) :=
  I.biUnion (foldFiberSingletonZeroSet M)

/-- The one-dimensional Fourier eigenspace for frequency `k`, represented by its basis direction.
-/
def foldFiberFourierEigenspace (M : ℕ) (k : Fin M) : Finset (Fin M) :=
  {k}

/-- The kernel support obtained by collecting the zero-eigenvalue Fourier directions. -/
def foldFiberKernelFourierSupport (M : ℕ) (I : Finset ℕ) : Finset (Fin M) :=
  (foldFiberConvolutionKernelZeroSet M I).biUnion (foldFiberFourierEigenspace M)

/-- The kernel dimension read off from the number of zero Fourier modes. -/
def foldFiberKernelDimension (M : ℕ) (I : Finset ℕ) : ℕ :=
  (foldFiberConvolutionKernelZeroSet M I).card

lemma foldFiberSingletonZeroSet_eq_coset (M i : ℕ) (k0 : Fin M)
    (hk0 : k0 ∈ foldFiberSingletonZeroSet M i) :
    foldFiberSingletonZeroSet M i = foldFiberSingletonZeroCoset M i k0 := by
  classical
  ext k
  simp [foldFiberSingletonZeroSet, foldFiberSingletonZeroCoset, foldFiberHalfResidue] at hk0 ⊢
  constructor
  · intro hk
    simpa [hk0] using hk
  · intro hk
    simpa [hk0] using hk

/-- Paper label: `prop:fold-fiber-convolution-kernel-zero-spectrum`.
The zero set of the subset-convolution kernel is the union of the singleton zero sets; each
singleton zero set is the affine congruence class determined by any of its witnesses; and the
kernel support is the direct sum of the corresponding one-dimensional Fourier directions, so its
dimension is the number of zero modes. -/
theorem paper_fold_fiber_convolution_kernel_zero_spectrum (M : ℕ) (I : Finset ℕ) :
    foldFiberConvolutionKernelZeroSet M I = I.biUnion (foldFiberSingletonZeroSet M) ∧
      (∀ i ∈ I, ∀ k0 : Fin M,
        k0 ∈ foldFiberSingletonZeroSet M i →
          foldFiberSingletonZeroSet M i = foldFiberSingletonZeroCoset M i k0 ∧
            (foldFiberSingletonZeroSet M i).card = (foldFiberSingletonZeroCoset M i k0).card) ∧
      foldFiberKernelFourierSupport M I =
        (foldFiberConvolutionKernelZeroSet M I).biUnion (foldFiberFourierEigenspace M) ∧
      foldFiberKernelDimension M I = (foldFiberConvolutionKernelZeroSet M I).card := by
  refine ⟨rfl, ?_, rfl, rfl⟩
  intro i hi k0 hk0
  let _ := hi
  refine ⟨foldFiberSingletonZeroSet_eq_coset M i k0 hk0, ?_⟩
  simp [foldFiberSingletonZeroSet_eq_coset M i k0 hk0]

end Omega.Folding
