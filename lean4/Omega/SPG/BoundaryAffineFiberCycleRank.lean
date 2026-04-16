import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Omega.SPG

/-- The two-edge boundary operator used as a finite graph seed over `𝔽_p`. -/
def boundaryTwo (p : ℕ) (v : Fin 2 → ZMod p) : ZMod p :=
  v 0 + v 1

/-- The affine fiber over a prescribed boundary value `δ`. -/
def boundaryFiber (p : ℕ) (δ : ZMod p) :=
  {v : Fin 2 → ZMod p // boundaryTwo p v = δ}

/-- The cycle space, i.e. the kernel of the boundary operator. -/
def boundaryKernel (p : ℕ) :=
  boundaryFiber p 0

/-- Parametrization of every affine fiber by one free `𝔽_p` coordinate. -/
def boundaryFiberEquiv (p : ℕ) (δ : ZMod p) : ZMod p ≃ boundaryFiber p δ where
  toFun a :=
    ⟨fun
        | 0 => a
        | 1 => δ - a,
      by simp [boundaryTwo]⟩
  invFun v := v.1 0
  left_inv a := rfl
  right_inv v := by
    apply Subtype.ext
    funext i
    fin_cases i
    · rfl
    · apply (sub_eq_iff_eq_add).2
      simpa [add_comm] using v.2.symm

noncomputable instance boundaryFiberFintype (p : ℕ) [Fact p.Prime] (δ : ZMod p) :
    Fintype (boundaryFiber p δ) :=
  Fintype.ofEquiv (ZMod p) (boundaryFiberEquiv p δ)

/-- Every affine fiber is equivalent to the kernel, reflecting the affine-coset picture. -/
def boundaryTranslateEquiv (p : ℕ) (δ : ZMod p) :
    boundaryKernel p ≃ boundaryFiber p δ :=
  (boundaryFiberEquiv p (0 : ZMod p)).symm.trans (boundaryFiberEquiv p δ)

/-- The affine fiber has `p` points, hence `p^{r(f)}` for the seed Euler characteristic
    `r(f) = 2 - 2 + 1 = 1`.
    thm:spg-boundary-affine-fiber-cycle-rank -/
theorem paper_spg_boundary_affine_fiber_cycle_rank (p : ℕ) [Fact p.Prime] (δ : ZMod p) :
    Nonempty (boundaryKernel p ≃ boundaryFiber p δ) ∧
      Fintype.card (boundaryFiber p δ) = p ∧
      Fintype.card (boundaryFiber p δ) = p ^ (2 - 2 + 1) := by
  refine ⟨⟨boundaryTranslateEquiv p δ⟩, ?_, ?_⟩
  · simpa [ZMod.card] using (Fintype.card_congr (boundaryFiberEquiv p δ)).symm
  · rw [show Fintype.card (boundaryFiber p δ) = p by
      simpa [ZMod.card] using (Fintype.card_congr (boundaryFiberEquiv p δ)).symm]
    norm_num

end Omega.SPG
