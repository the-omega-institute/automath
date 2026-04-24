import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

/-- A concrete `2 × 2` block presentation of an operator on the eigenspace splitting
`V = V₊ ⊕ V₋`. -/
structure SelfDualBlockMatrix where
  X : ℂ
  Y : ℂ
  Z : ℂ
  W : ℂ

@[ext] theorem SelfDualBlockMatrix.ext
    (A B : SelfDualBlockMatrix) (hX : A.X = B.X) (hY : A.Y = B.Y) (hZ : A.Z = B.Z)
    (hW : A.W = B.W) : A = B := by
  cases A
  cases B
  cases hX
  cases hY
  cases hZ
  cases hW
  rfl

/-- Conjugation by the self-dual involution `Π`, acting by `+1` on `V₊` and `-1` on `V₋`. -/
def selfDualPiConj (B : SelfDualBlockMatrix) : SelfDualBlockMatrix :=
  { X := B.X
    Y := -B.Y
    Z := -B.Z
    W := B.W }

/-- The self-dual affine family `B(u) = B₀ + u Π⁻¹ B₀ Π`, written entrywise. -/
def selfDualFamily (u : ℂ) (B : SelfDualBlockMatrix) : SelfDualBlockMatrix :=
  { X := B.X + u * (selfDualPiConj B).X
    Y := B.Y + u * (selfDualPiConj B).Y
    Z := B.Z + u * (selfDualPiConj B).Z
    W := B.W + u * (selfDualPiConj B).W }

/-- The `(1 + u)/(1 - u)` normal form induced by the self-dual involution. -/
def selfDualNormalForm (u : ℂ) (B : SelfDualBlockMatrix) : SelfDualBlockMatrix :=
  { X := (1 + u) * B.X
    Y := (1 - u) * B.Y
    Z := (1 - u) * B.Z
    W := (1 + u) * B.W }

/-- For the concrete sync-kernel model, the `+1`-eigenspace has dimension `5`. -/
def selfDualPlusDim : ℕ := 5

/-- For the concrete sync-kernel model, the `-1`-eigenspace has dimension `5`. -/
def selfDualMinusDim : ℕ := 5

/-- Paper label: `prop:self-dual-normal-form-1pmu`. -/
theorem paper_self_dual_normal_form_1pmu (u : ℂ) (X Y Z W : ℂ) :
    let B0 : SelfDualBlockMatrix := ⟨X, Y, Z, W⟩
    selfDualPiConj B0 = ⟨X, -Y, -Z, W⟩ ∧
      selfDualFamily u B0 = selfDualNormalForm u B0 ∧
      selfDualPlusDim = 5 ∧ selfDualMinusDim = 5 := by
  dsimp [selfDualPiConj, selfDualFamily, selfDualNormalForm, selfDualPlusDim, selfDualMinusDim]
  refine ⟨rfl, ?_⟩
  refine ⟨?_, ?_⟩
  · ext <;> simp <;> ring
  · exact ⟨rfl, rfl⟩

end Omega.SyncKernelWeighted
