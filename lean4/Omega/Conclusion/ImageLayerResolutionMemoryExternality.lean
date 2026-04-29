import Mathlib.Tactic
import Omega.Conclusion.ImageLayerMinimalInverseMemory

namespace Omega.Conclusion

/-- The image-layer conjugacy datum after all `m ≥ 3` image layers collapse to the same full-shift
topological type. -/
def conclusion_image_layer_resolution_annihilation_sync_externality_imageInvariant
    (_m : ℕ) : PUnit.{0} :=
  PUnit.unit

/-- Concrete invariant statement: the image-layer datum is constant for all `m ≥ 3`, whereas
`dSync m = m - 1` is strictly monotone and neither resolution nor sync debt is recoverable from
that collapsed image-layer datum. -/
def conclusion_image_layer_resolution_annihilation_sync_externality_statement : Prop :=
  (∀ m n : ℕ, 3 ≤ m → 3 ≤ n →
    conclusion_image_layer_resolution_annihilation_sync_externality_imageInvariant m =
      conclusion_image_layer_resolution_annihilation_sync_externality_imageInvariant n) ∧
    (∀ m : ℕ, 3 ≤ m → dSync m = m - 1) ∧
    (∀ m n : ℕ, 3 ≤ m → m < n → dSync m < dSync n) ∧
    (¬ ∃ recoverResolution : PUnit.{0} → ℕ,
      ∀ m : ℕ, 3 ≤ m →
        recoverResolution
            (conclusion_image_layer_resolution_annihilation_sync_externality_imageInvariant m) =
          m) ∧
    (¬ ∃ recoverDebt : PUnit.{0} → ℕ,
      ∀ m : ℕ, 3 ≤ m →
        recoverDebt
            (conclusion_image_layer_resolution_annihilation_sync_externality_imageInvariant m) =
          dSync m)

/-- Paper label: `thm:conclusion-image-layer-resolution-annihilation-sync-externality`. -/
theorem paper_conclusion_image_layer_resolution_annihilation_sync_externality :
    conclusion_image_layer_resolution_annihilation_sync_externality_statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro m n hm hn
    rfl
  · intro m hm
    exact dSync_eq m
  · intro m n hm hmn
    exact dSync_strict_mono hm hmn
  · rintro ⟨recoverResolution, hrecoverResolution⟩
    have h3 := hrecoverResolution 3 (by norm_num)
    have h4 := hrecoverResolution 4 (by norm_num)
    simp at h3 h4
    omega
  · rintro ⟨recoverDebt, hrecoverDebt⟩
    have h3 := hrecoverDebt 3 (by norm_num)
    have h4 := hrecoverDebt 4 (by norm_num)
    simp [dSync] at h3 h4
    omega

end Omega.Conclusion
