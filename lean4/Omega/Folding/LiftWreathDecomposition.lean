import Mathlib.Tactic

namespace Omega.Folding

universe u v w z

/-- Fiberwise data consisting of the induced permutation of the size strata together with the
permutations inside each fixed-size fiber. -/
structure FiberwiseWreathDatum (ι : Type u) (G : Type v) (H : ι → Type w) where
  global : G
  fiberwise : (i : ι) → H i

@[ext] theorem FiberwiseWreathDatum.ext
    {ι : Type u} {G : Type v} {H : ι → Type w}
    {ρ₁ ρ₂ : FiberwiseWreathDatum ι G H}
    (hglobal : ρ₁.global = ρ₂.global)
    (hfiberwise : ∀ i, ρ₁.fiberwise i = ρ₂.fiberwise i) :
    ρ₁ = ρ₂ := by
  cases ρ₁ with
  | mk g₁ f₁ =>
      cases ρ₂ with
      | mk g₂ f₂ =>
          cases hglobal
          have hfun : f₁ = f₂ := funext hfiberwise
          cases hfun
          rfl

/-- Chapter-local package for the fold-lift wreath decomposition. The data record a partition of
the observable space by fiber size together with the decomposition of each lift into its induced
permutation of the size strata and its family of within-fiber permutations. -/
structure LiftWreathDecompositionData where
  X : Type u
  FiberSize : Type v
  Lift : Type w
  GlobalPerm : Type z
  FiberPerm : FiberSize → Type z
  fiberSize : X → FiberSize
  liftOne : Lift
  liftMul : Lift → Lift → Lift
  globalOne : GlobalPerm
  globalMul : GlobalPerm → GlobalPerm → GlobalPerm
  fiberOne : (d : FiberSize) → FiberPerm d
  fiberMul : (d : FiberSize) → FiberPerm d → FiberPerm d → FiberPerm d
  inducedPerm : Lift → GlobalPerm
  withinFiberPerm : (d : FiberSize) → Lift → FiberPerm d
  assemble : FiberwiseWreathDatum FiberSize GlobalPerm FiberPerm → Lift
  assemble_decompose :
    ∀ τ,
      assemble
          ⟨inducedPerm τ, fun d => withinFiberPerm d τ⟩ = τ
  decompose_assemble :
    ∀ ρ,
      inducedPerm (assemble ρ) = ρ.global ∧
        (∀ d, withinFiberPerm d (assemble ρ) = ρ.fiberwise d)
  induced_one : inducedPerm liftOne = globalOne
  within_one : ∀ d, withinFiberPerm d liftOne = fiberOne d
  induced_mul : ∀ τ₁ τ₂, inducedPerm (liftMul τ₁ τ₂) = globalMul (inducedPerm τ₁) (inducedPerm τ₂)
  within_mul :
    ∀ d τ₁ τ₂,
      withinFiberPerm d (liftMul τ₁ τ₂) =
        fiberMul d (withinFiberPerm d τ₁) (withinFiberPerm d τ₂)

/-- The decomposition map from a lift to its induced permutation on the strata `X(d)` together
with the fiberwise permutations. -/
def decomposeLiftWreathDatum (D : LiftWreathDecompositionData) :
    D.Lift → FiberwiseWreathDatum D.FiberSize D.GlobalPerm D.FiberPerm :=
  fun τ => ⟨D.inducedPerm τ, fun d => D.withinFiberPerm d τ⟩

/-- The neutral element in the target fiberwise wreath datum. -/
def liftWreathDatumOne (D : LiftWreathDecompositionData) :
    FiberwiseWreathDatum D.FiberSize D.GlobalPerm D.FiberPerm :=
  ⟨D.globalOne, D.fiberOne⟩

/-- Fiberwise multiplication in the target wreath datum. -/
def liftWreathDatumMul (D : LiftWreathDecompositionData)
    (ρ₁ ρ₂ : FiberwiseWreathDatum D.FiberSize D.GlobalPerm D.FiberPerm) :
    FiberwiseWreathDatum D.FiberSize D.GlobalPerm D.FiberPerm :=
  ⟨D.globalMul ρ₁.global ρ₂.global, fun d => D.fiberMul d (ρ₁.fiberwise d) (ρ₂.fiberwise d)⟩

/-- Paper-facing wreath decomposition for fold lifts: partition by fiber size, send a lift to the
induced permutation on each stratum together with its within-fiber permutations, and reconstruct
the inverse map fiberwise.
    thm:fold-lift-wreath-decomposition -/
theorem paper_fold_lift_wreath_decomposition (D : LiftWreathDecompositionData) :
    Function.Bijective (decomposeLiftWreathDatum D) ∧
      Function.LeftInverse D.assemble (decomposeLiftWreathDatum D) ∧
      Function.RightInverse D.assemble (decomposeLiftWreathDatum D) ∧
      decomposeLiftWreathDatum D D.liftOne = liftWreathDatumOne D ∧
      (∀ τ₁ τ₂,
        decomposeLiftWreathDatum D (D.liftMul τ₁ τ₂) =
          liftWreathDatumMul D (decomposeLiftWreathDatum D τ₁) (decomposeLiftWreathDatum D τ₂)) := by
  have hLeft : Function.LeftInverse D.assemble (decomposeLiftWreathDatum D) := D.assemble_decompose
  have hRight : Function.RightInverse D.assemble (decomposeLiftWreathDatum D) := by
    intro ρ
    ext d <;> simp [decomposeLiftWreathDatum, D.decompose_assemble ρ]
  refine ⟨⟨hLeft.injective, hRight.surjective⟩, hLeft, hRight, ?_, ?_⟩
  · ext d <;> simp [decomposeLiftWreathDatum, liftWreathDatumOne, D.induced_one, D.within_one]
  · intro τ₁ τ₂
    ext d <;>
      simp [decomposeLiftWreathDatum, liftWreathDatumMul, D.induced_mul, D.within_mul]

end Omega.Folding
