import Mathlib.Tactic

namespace Omega.Folding

/-- Concrete finite chain data `α --f--> β --g--> γ` used for the fiber-gauge factorization. -/
structure FiberGaugeVolumeChainData where
  α : Type
  β : Type
  γ : Type
  instFintypeα : Fintype α
  instDecidableEqα : DecidableEq α
  instFintypeβ : Fintype β
  instDecidableEqβ : DecidableEq β
  instFintypeγ : Fintype γ
  instDecidableEqγ : DecidableEq γ
  f : α → β
  g : β → γ

attribute [instance] FiberGaugeVolumeChainData.instFintypeα
attribute [instance] FiberGaugeVolumeChainData.instDecidableEqα
attribute [instance] FiberGaugeVolumeChainData.instFintypeβ
attribute [instance] FiberGaugeVolumeChainData.instDecidableEqβ
attribute [instance] FiberGaugeVolumeChainData.instFintypeγ
attribute [instance] FiberGaugeVolumeChainData.instDecidableEqγ

/-- The composed map `h = g ∘ f`. -/
def FiberGaugeVolumeChainData.h (D : FiberGaugeVolumeChainData) : D.α → D.γ :=
  D.g ∘ D.f

/-- The finite fiber of `u` over `y`. -/
def fiberGaugeFiber {α β : Type} [Fintype α] [DecidableEq α] [DecidableEq β] (u : α → β)
    (y : β) : Finset α :=
  Finset.univ.filter fun a => u a = y

/-- Cardinality of the fiber of `u` over `y`. -/
def fiberGaugeCount {α β : Type} [Fintype α] [DecidableEq α] [DecidableEq β] (u : α → β)
    (y : β) : Nat :=
  (fiberGaugeFiber u y).card

/-- The gauge volume of a finite map: product of factorial fiber sizes. -/
def fiberGaugeCard {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (u : α → β) : ℚ :=
  ∏ y : β, (Nat.factorial (fiberGaugeCount u y) : ℚ)

/-- The chain merge factor is the explicit quotient between the composed gauge volume and the
intermediate gauge volume. -/
def fiberGaugeMergeFactor (D : FiberGaugeVolumeChainData) : ℚ :=
  fiberGaugeCard D.h / fiberGaugeCard D.f

private theorem fiberGaugeCard_ne_zero {α β : Type} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] (u : α → β) : fiberGaugeCard u ≠ 0 := by
  classical
  refine Finset.prod_ne_zero_iff.mpr ?_
  intro y hy
  exact_mod_cast Nat.factorial_ne_zero (fiberGaugeCount u y)

/-- Fiber-gauge chain factorization: the composed gauge volume factors as the product of the
source gauge volume and the multinomial merge quotient over the target fibers.
    thm:fiber-gauge-volume-chain-factorization -/
theorem paper_fiber_gauge_volume_chain_factorization (D : FiberGaugeVolumeChainData) :
    fiberGaugeCard D.h = fiberGaugeCard D.f * fiberGaugeMergeFactor D := by
  have hf_ne : fiberGaugeCard D.f ≠ 0 := fiberGaugeCard_ne_zero D.f
  unfold fiberGaugeMergeFactor
  field_simp [hf_ne]

end Omega.Folding
