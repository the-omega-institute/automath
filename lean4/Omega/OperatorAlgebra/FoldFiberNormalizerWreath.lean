import Mathlib

namespace Omega.OperatorAlgebra

open scoped BigOperators

/-- Visible permutations that preserve the fold-fiber cardinality profile. -/
def CompatibleVisiblePerm {m : ℕ} (d : Fin m → ℕ) :=
  {f : Equiv.Perm (Fin m) // ∀ x, d (f x) = d x}

noncomputable instance compatibleVisiblePermFintype {m : ℕ} (d : Fin m → ℕ) :
    Fintype (CompatibleVisiblePerm d) := by
  classical
  unfold CompatibleVisiblePerm
  infer_instance

/-- The hidden fiberwise automorphisms carried by each visible state. -/
def HiddenFiberAutomorphisms {m : ℕ} (d : Fin m → ℕ) :=
  (x : Fin m) → Equiv.Perm (Fin (d x))

noncomputable instance hiddenFiberAutomorphismsFintype {m : ℕ} (d : Fin m → ℕ) :
    Fintype (HiddenFiberAutomorphisms d) := by
  classical
  unfold HiddenFiberAutomorphisms
  infer_instance

/-- Finite proxy for the fold-compatible normalizer: a visible permutation preserving the fiber
profile together with a permutation acting inside each fiber. -/
def FoldFiberNormalizer {m : ℕ} (d : Fin m → ℕ) :=
  CompatibleVisiblePerm d × HiddenFiberAutomorphisms d

noncomputable instance foldFiberNormalizerFintype {m : ℕ} (d : Fin m → ℕ) :
    Fintype (FoldFiberNormalizer d) := by
  classical
  unfold FoldFiberNormalizer
  infer_instance

/-- The visible action induced by a fold-compatible normalizer element. -/
def visibleProjection {m : ℕ} (d : Fin m → ℕ) :
    FoldFiberNormalizer d → CompatibleVisiblePerm d :=
  Prod.fst

/-- Identity element of the visible compatible-permutation factor. -/
def visibleIdentity {m : ℕ} (d : Fin m → ℕ) : CompatibleVisiblePerm d :=
  ⟨Equiv.refl _, by intro x; rfl⟩

/-- Fiberwise automorphisms, viewed as the kernel of the visible projection. -/
def fiberwiseAutomorphismKernel {m : ℕ} (d : Fin m → ℕ) : Set (FoldFiberNormalizer d) :=
  {τ | visibleProjection d τ = visibleIdentity d}

/-- Noncanonical section obtained by choosing the identity labeling on every hidden fiber. -/
def visibleSection {m : ℕ} (d : Fin m → ℕ) :
    CompatibleVisiblePerm d → FoldFiberNormalizer d :=
  fun f => (f, fun x => Equiv.refl (Fin (d x)))

/-- Finite fold proxy for the normalizer exactness and wreath decomposition: the visible projection
is surjective with a section, its kernel is exactly the fiberwise automorphism subgroup, and the
normalizer splits as the product of the visible compatible permutations with the hidden fiberwise
automorphisms. The hidden factor has cardinality `∏_x d(x)!`, giving the expected wreath-style
counting formula.
    thm:op-algebra-fold-fiber-normalizer-wreath -/
theorem paper_op_algebra_fold_fiber_normalizer_wreath :
    ∀ {m : ℕ} (d : Fin m → ℕ),
      Function.Surjective (visibleProjection d) ∧
        (∀ τ : FoldFiberNormalizer d,
          visibleProjection d τ = visibleIdentity d ↔ τ ∈ fiberwiseAutomorphismKernel d) ∧
        (∀ f : CompatibleVisiblePerm d, visibleProjection d (visibleSection d f) = f) ∧
        Nonempty (FoldFiberNormalizer d ≃ CompatibleVisiblePerm d × HiddenFiberAutomorphisms d) ∧
        Fintype.card (HiddenFiberAutomorphisms d) = ∏ x, Nat.factorial (d x) ∧
        Fintype.card (FoldFiberNormalizer d) =
          Fintype.card (CompatibleVisiblePerm d) * ∏ x, Nat.factorial (d x) := by
  intro m d
  classical
  have hHiddenCard : Fintype.card (HiddenFiberAutomorphisms d) = ∏ x, Nat.factorial (d x) := by
    simpa [HiddenFiberAutomorphisms, Fintype.card_perm] using
      (Fintype.card_pi : Fintype.card ((x : Fin m) → Equiv.Perm (Fin (d x))) =
        ∏ x, Fintype.card (Equiv.Perm (Fin (d x))))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f
    exact ⟨visibleSection d f, rfl⟩
  · intro τ
    rfl
  · intro f
    rfl
  · exact ⟨Equiv.refl _⟩
  · exact hHiddenCard
  · have hProd :
        Fintype.card (FoldFiberNormalizer d) =
          Fintype.card (CompatibleVisiblePerm d) * Fintype.card (HiddenFiberAutomorphisms d) := by
      simpa [FoldFiberNormalizer] using
        (Fintype.card_prod (CompatibleVisiblePerm d) (HiddenFiberAutomorphisms d))
    calc
      Fintype.card (FoldFiberNormalizer d)
          = Fintype.card (CompatibleVisiblePerm d) * Fintype.card (HiddenFiberAutomorphisms d) := hProd
      _ = Fintype.card (CompatibleVisiblePerm d) * ∏ x, Nat.factorial (d x) := by
            rw [hHiddenCard]

end Omega.OperatorAlgebra
