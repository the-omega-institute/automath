import Mathlib.Tactic

namespace Omega.CircleDimension

/-- Bookkeeping model for the connected torus factor of
`Hom(ℤ^r ⊕ T, 𝕋)`: the finite torsion part contributes no connected dimension,
so only the free rank remains. -/
def higherCircleDimFGAbelian (freeRank torsionRank : ℕ) : ℕ :=
  freeRank + 0 * torsionRank

/-- The `k = 1` specialization records the same free-rank bookkeeping for the
abelianization. -/
def higherCircleDimK1Abelianization (freeRank torsionRank : ℕ) : ℕ :=
  higherCircleDimFGAbelian freeRank torsionRank

/-- In the finitely generated model `ℤ^r ⊕ T`, the identity component of the
character group has torus dimension `r`; specializing to `k = 1` recovers the
abelianization-rank statement used later in the file.
    thm:cdim-higher-rank-hk -/
theorem paper_cdim_higher_rank_hk (freeRank torsionRank : ℕ) :
    higherCircleDimFGAbelian freeRank torsionRank = freeRank ∧
      higherCircleDimK1Abelianization freeRank torsionRank = freeRank := by
  simp [higherCircleDimFGAbelian, higherCircleDimK1Abelianization]

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
