import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Abelianization.Defs

namespace Omega.Conclusion

/-- The conclusion chapter formulation: the commutator subgroup is the intersection of all
surviving layer-character kernels. -/
def conclusion_fold_normalizer_commutator_kernel_statement
    {G ι : Type*} [Group G]
    (layerCharacter : ι → G →* Multiplicative (ZMod 2))
    (layeredParity : G →* (ι → Multiplicative (ZMod 2))) : Prop :=
  commutator G = layeredParity.ker ∧ commutator G = ⨅ i, (layerCharacter i).ker

/-- Paper label: `prop:conclusion-fold-normalizer-commutator-kernel`. -/
theorem paper_conclusion_fold_normalizer_commutator_kernel
    {G ι : Type*} [Group G]
    (layerCharacter : ι → G →* Multiplicative (ZMod 2))
    (layeredParity : G →* (ι → Multiplicative (ZMod 2)))
    (hlayeredParity_apply : ∀ g i, layeredParity g i = layerCharacter i g)
    (habelianization_kernel : commutator G = layeredParity.ker) :
    conclusion_fold_normalizer_commutator_kernel_statement layerCharacter layeredParity := by
  classical
  refine ⟨habelianization_kernel, ?_⟩
  rw [habelianization_kernel]
  ext g
  simp only [MonoidHom.mem_ker, Subgroup.mem_iInf]
  constructor
  · intro hg i
    have hi := congrFun hg i
    rwa [hlayeredParity_apply] at hi
  · intro hg
    ext i
    rw [hlayeredParity_apply, hg i]
    rfl

end Omega.Conclusion
