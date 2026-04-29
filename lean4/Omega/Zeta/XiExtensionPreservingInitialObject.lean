import Mathlib

namespace Omega.Zeta

/-- An extension-preserving record with the four mandatory components used in the paper-level
construction. -/
structure XiExtensionPreservingRecord where
  base : ℝ
  left : ℝ
  right : ℝ
  extension : ℝ

@[ext]
theorem XiExtensionPreservingRecord.ext
    {r s : XiExtensionPreservingRecord}
    (hbase : r.base = s.base)
    (hleft : r.left = s.left)
    (hright : r.right = s.right)
    (hext : r.extension = s.extension) : r = s := by
  cases r
  cases s
  cases hbase
  cases hleft
  cases hright
  cases hext
  rfl

/-- In the thin extension-preserving category, a morphism is an equality of records. -/
def extensionPreservingHom (r s : XiExtensionPreservingRecord) : Prop :=
  r = s

/-- Finite data for the extension-preserving initial-object statement. The canonical object is
assembled from four distinguished components, and the orthogonal trichotomy together with the
minimality hypothesis identifies every other object with it. -/
structure XiExtensionPreservingInitialObjectData where
  objectCount : ℕ
  baseComponent : ℝ
  leftComponent : ℝ
  rightComponent : ℝ
  extensionComponent : ℝ
  object : Fin objectCount → XiExtensionPreservingRecord
  orthogonalTrichotomy :
    ∀ i : Fin objectCount,
      (object i).base = baseComponent ∧
        (object i).left = leftComponent ∧
        (object i).right = rightComponent
  minimalExtension :
    ∀ i : Fin objectCount, (object i).extension = extensionComponent

namespace XiExtensionPreservingInitialObjectData

/-- The canonical record axis `r₀` obtained from the four mandatory components. -/
def canonicalRecord (D : XiExtensionPreservingInitialObjectData) : XiExtensionPreservingRecord where
  base := D.baseComponent
  left := D.leftComponent
  right := D.rightComponent
  extension := D.extensionComponent

/-- The canonical record is initial when every extension-preserving record admits a unique
factorization through it. -/
def HasInitialObject (D : XiExtensionPreservingInitialObjectData) : Prop :=
  ∀ i : Fin D.objectCount,
    ∃! _ : extensionPreservingHom D.canonicalRecord (D.object i), True

end XiExtensionPreservingInitialObjectData

/-- Paper label: `thm:xi-extension-preserving-initial-object`. The canonical four-component record
is initial in the thin extension-preserving category because every other record agrees with it
componentwise, hence factors through it uniquely. -/
theorem paper_xi_extension_preserving_initial_object (D : XiExtensionPreservingInitialObjectData) :
    D.HasInitialObject := by
  intro i
  rcases D.orthogonalTrichotomy i with ⟨hbase, hleft, hright⟩
  have hext := D.minimalExtension i
  refine ⟨?_, trivial, ?_⟩
  · dsimp [extensionPreservingHom]
    ext
    · simpa [XiExtensionPreservingInitialObjectData.canonicalRecord] using hbase.symm
    · simpa [XiExtensionPreservingInitialObjectData.canonicalRecord] using hleft.symm
    · simpa [XiExtensionPreservingInitialObjectData.canonicalRecord] using hright.symm
    · simpa [XiExtensionPreservingInitialObjectData.canonicalRecord] using hext.symm
  · intro _ hf
    exact Subsingleton.elim _ _

end Omega.Zeta
