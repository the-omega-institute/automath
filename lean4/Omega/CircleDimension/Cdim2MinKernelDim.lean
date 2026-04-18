import Mathlib.Tactic

namespace Omega.CircleDimension

/-- A second cohomology class factors through a `d`-dimensional torus when its support torus of
dimension `supportDim` is enlarged by `kernelDim` extra circle directions inside an ambient torus
of dimension `ambientDim`. -/
def cdim2FactorsThroughSubtorus (supportDim ambientDim d : ℕ) : Prop :=
  ∃ kernelDim, d = supportDim + kernelDim ∧ d ≤ ambientDim

/-- The support torus is contained in a `d`-dimensional subtorus of the ambient `ambientDim`-torus.
-/
def cdim2SupportedOnSubtorus (supportDim ambientDim d : ℕ) : Prop :=
  supportDim ≤ d ∧ d ≤ ambientDim

/-- The minimal realizable dimension is the support-torus dimension itself. -/
def cdim2MinKernelDim (_ambientDim supportDim : ℕ) : ℕ :=
  supportDim

/-- The finite-rank support-torus certificate for second circle dimension: factorization through a
`d`-torus is equivalent to containment in a `d`-dimensional subtorus, and the minimal such `d`
is exactly the support-torus dimension.
    thm:cdim2-min-kernel-dim -/
theorem paper_cdim2_min_kernel_dim (supportDim ambientDim d : ℕ) (hs : supportDim ≤ ambientDim) :
    (cdim2FactorsThroughSubtorus supportDim ambientDim d ↔
      cdim2SupportedOnSubtorus supportDim ambientDim d) ∧
    cdim2FactorsThroughSubtorus supportDim ambientDim
      (cdim2MinKernelDim ambientDim supportDim) ∧
    (cdim2FactorsThroughSubtorus supportDim ambientDim d →
      cdim2MinKernelDim ambientDim supportDim ≤ d) := by
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · rintro ⟨kernelDim, hk, hd⟩
      refine ⟨by simpa [hk] using Nat.le_add_right supportDim kernelDim, ?_⟩
      simpa [hk] using hd
    · rintro ⟨hSupport, hd⟩
      rcases Nat.exists_eq_add_of_le hSupport with ⟨kernelDim, hk⟩
      exact ⟨kernelDim, hk, hd⟩
  · exact ⟨0, by simp [cdim2MinKernelDim, hs]⟩
  · rintro ⟨kernelDim, hk, _hd⟩
    rw [cdim2MinKernelDim, hk]
    exact Nat.le_add_right supportDim kernelDim

end Omega.CircleDimension
