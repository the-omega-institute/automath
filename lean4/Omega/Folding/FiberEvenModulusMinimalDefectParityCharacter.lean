import Mathlib.Tactic
import Omega.Folding.FiberConvolutionKernelZeroSpectrum

namespace Omega.Folding

/-- Paper label: `cor:fold-fiber-even-modulus-minimal-defect-parity-character`.
For the singleton shift `{1}`, the zero spectrum consists of the unique half-modulus residue, so
the kernel has dimension `1`. -/
theorem paper_fold_fiber_even_modulus_minimal_defect_parity_character (m : Nat)
    (hEven : Even (Nat.fib (m + 2))) :
    Omega.Folding.foldFiberKernelDimension (Nat.fib (m + 2)) ({1} : Finset Nat) = 1 := by
  let M := Nat.fib (m + 2)
  have hMpos : 0 < M := by
    dsimp [M]
    exact Nat.fib_pos.mpr (by omega)
  have hhalf_lt : M / 2 < M := Nat.div_lt_self hMpos (by decide)
  have hsingleton : foldFiberSingletonZeroSet M 1 = {⟨M / 2, hhalf_lt⟩} := by
    ext k
    have hkmod : k.1 % M = k.1 := Nat.mod_eq_of_lt k.2
    constructor
    · intro hk
      simp [foldFiberSingletonZeroSet, foldFiberHalfResidue, hkmod] at hk
      simp [hk, Fin.ext_iff]
    · intro hk
      simp [foldFiberSingletonZeroSet, foldFiberHalfResidue, hkmod] at hk ⊢
      simpa [Fin.ext_iff] using hk
  let _ := hEven
  have hcard : (foldFiberSingletonZeroSet M 1).card = 1 := by
    rw [hsingleton]
    simp
  unfold foldFiberKernelDimension foldFiberConvolutionKernelZeroSet
  simpa [M] using hcard

end Omega.Folding
