import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic
import Omega.GU.BdryUpliftOrientationParity

namespace Omega.GU

open scoped BigOperators

/-- The four odd fibers in the window-6 block decomposition. -/
abbrev Window6OddFiber := Fin 4

/-- The odd-fiber block-orientation gauge data: one `S₃` orientation action per odd fiber. -/
abbrev Window6OddFiberGauge := Window6OddFiber → Equiv.Perm (Fin 3)

/-- The per-fiber sign character recording the orientation action on the `i`-th odd fiber. -/
noncomputable def window6FiberOrientationCharacter (i : Window6OddFiber) :
    Window6OddFiberGauge →* ℤˣ where
  toFun σ := upliftOrientationParity 3 (σ i)
  map_one' := by
    simp [upliftOrientationParity, signHom]
  map_mul' σ τ := by
    simp [upliftOrientationParity, signHom]

/-- The global even-parity character is the product of the four odd-fiber sign characters. -/
noncomputable def window6ProductSign : Window6OddFiberGauge →* ℤˣ where
  toFun σ := ∏ i, window6FiberOrientationCharacter i σ
  map_one' := by
    simp [window6FiberOrientationCharacter]
  map_mul' σ τ := by
    simp [window6FiberOrientationCharacter, Finset.prod_mul_distrib]

/-- Two window-6 gauge configurations lie in the same global even-parity orientation torsor
    exactly when they have the same product sign. -/
def window6GlobalEvenParityOrientationTorsor (σ τ : Window6OddFiberGauge) : Prop :=
  window6ProductSign σ = window6ProductSign τ

/-- The stabilizer of the neutral orientation torsor point. -/
def window6GlobalEvenParityStabilizer (σ : Window6OddFiberGauge) : Prop :=
  window6GlobalEvenParityOrientationTorsor σ 1

/-- The product-sign kernel of the window-6 odd-fiber gauge action. -/
def window6ProductSignKernel (σ : Window6OddFiberGauge) : Prop :=
  window6ProductSign σ = 1

/-- The neutral-orientation stabilizer is exactly the product-sign kernel. -/
theorem window6GlobalEvenParityStabilizer_iff_kernel (σ : Window6OddFiberGauge) :
    window6GlobalEvenParityStabilizer σ ↔ window6ProductSignKernel σ := by
  simp [window6GlobalEvenParityStabilizer, window6GlobalEvenParityOrientationTorsor,
    window6ProductSignKernel]

/-- Paper-facing corollary for the window-6 global even-parity orientation torsor: the odd-fiber
    block decomposition has four blocks, the gauge action factors through four sign characters,
    and the stabilizer is the product-sign kernel.
    cor:window6-foldbin-global-even-parity-orientation-torsor -/
theorem paper_window6_foldbin_global_even_parity_orientation_torsor :
    Fintype.card Window6OddFiber = 4 ∧
      (∀ i : Window6OddFiber, ∀ σ : Window6OddFiberGauge,
        window6FiberOrientationCharacter i σ = upliftOrientationParity 3 (σ i)) ∧
      (∀ σ : Window6OddFiberGauge,
        window6ProductSign σ = ∏ i, window6FiberOrientationCharacter i σ) ∧
      (∀ σ : Window6OddFiberGauge,
        window6GlobalEvenParityStabilizer σ ↔ window6ProductSignKernel σ) := by
  refine ⟨by simp [Window6OddFiber], ?_, ?_, ?_⟩
  · intro i σ
    rfl
  · intro σ
    rfl
  · intro σ
    exact window6GlobalEvenParityStabilizer_iff_kernel σ

end Omega.GU
