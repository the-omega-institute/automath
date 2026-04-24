import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Conclusion

/-- Finite-support coefficient data for Smith `p`-kernel spectrum functions. -/
structure SmithPKernelSpectrumConeSimplicialData where
  rank : ℕ
  coeff : ℕ → ℕ
  coeff_zero_of_ge : ∀ l, rank ≤ l → coeff l = 0

namespace SmithPKernelSpectrumConeSimplicialData

def smithAtom (l k : ℕ) : ℕ :=
  min k (l + 1)

def kernelOfFamily (D : SmithPKernelSpectrumConeSimplicialData) (f : ℕ → ℕ) (k : ℕ) : ℕ :=
  Finset.sum (Finset.range D.rank) (fun l => f l * SmithPKernelSpectrumConeSimplicialData.smithAtom l k)

def kernel (D : SmithPKernelSpectrumConeSimplicialData) (k : ℕ) : ℕ :=
  D.kernelOfFamily D.coeff k

def singleAtomFamily (l : ℕ) : ℕ → ℕ :=
  fun j => if j = l then 1 else 0

def freeCommutativeMonoidModel (D : SmithPKernelSpectrumConeSimplicialData) : Prop :=
  ∃ f : ℕ → ℕ, (∀ l, D.rank ≤ l → f l = 0) ∧ ∀ k, D.kernel k = D.kernelOfFamily f k

def simplicialCone (D : SmithPKernelSpectrumConeSimplicialData) : Prop :=
  ∀ k, 0 ≤ D.kernel k

def atomicExtremeRays (D : SmithPKernelSpectrumConeSimplicialData) : Prop :=
  ∀ l,
    l < D.rank →
      ∀ k,
        D.kernelOfFamily (SmithPKernelSpectrumConeSimplicialData.singleAtomFamily l) k =
          SmithPKernelSpectrumConeSimplicialData.smithAtom l k

end SmithPKernelSpectrumConeSimplicialData

open SmithPKernelSpectrumConeSimplicialData

theorem paper_conclusion_smith_p_kernel_spectrum_cone_simplicial
    (D : SmithPKernelSpectrumConeSimplicialData) :
    D.freeCommutativeMonoidModel ∧ D.simplicialCone ∧ D.atomicExtremeRays := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨D.coeff, D.coeff_zero_of_ge, ?_⟩
    intro k
    rfl
  · intro k
    exact Nat.zero_le (D.kernel k)
  · intro l hl k
    have hlmem : l ∈ Finset.range D.rank := Finset.mem_range.mpr hl
    unfold SmithPKernelSpectrumConeSimplicialData.kernelOfFamily
    rw [Finset.sum_eq_single_of_mem l hlmem]
    · simp [SmithPKernelSpectrumConeSimplicialData.singleAtomFamily,
        SmithPKernelSpectrumConeSimplicialData.smithAtom]
    · intro j hj hjl
      simp [SmithPKernelSpectrumConeSimplicialData.singleAtomFamily,
        SmithPKernelSpectrumConeSimplicialData.smithAtom, hjl]

end Omega.Conclusion
