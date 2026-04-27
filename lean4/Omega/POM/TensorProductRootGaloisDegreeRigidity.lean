import Mathlib.Data.Set.Finite.Range
import Mathlib.Tactic

namespace Omega.POM

/-- The concrete finite range instance for the product-root map used in the orbit count. -/
noncomputable instance pom_tensor_product_root_galois_degree_rigidity_fintype_range {ι α : Type*}
    [Fintype ι] [DecidableEq α] (Root : ι → Type*) [∀ i, Fintype (Root i)]
    (mulRoot : ((i : ι) → Root i) → α) : Fintype (Set.range mulRoot) := by
  classical
  exact Set.fintypeRange mulRoot

/-- Paper label: `thm:pom-tensor-product-root-galois-degree-rigidity`.
An injective product-root orbit has cardinality equal to the product of the root
set cardinalities, so any degree identified with that orbit cardinal has the same value. -/
theorem paper_pom_tensor_product_root_galois_degree_rigidity {ι α : Type*} [Fintype ι]
    [DecidableEq α] (Root : ι → Type*) [∀ i, Fintype (Root i)]
    (mulRoot : ((i : ι) → Root i) → α) (hNoCollision : Function.Injective mulRoot)
    (minpolyDegree : ℕ) (hDegree : minpolyDegree = Fintype.card (Set.range mulRoot)) :
    minpolyDegree = ∏ i, Fintype.card (Root i) := by
  classical
  calc
    minpolyDegree = Fintype.card (Set.range mulRoot) := hDegree
    _ = Fintype.card ((i : ι) → Root i) := Set.card_range_of_injective hNoCollision
    _ = ∏ i, Fintype.card (Root i) := Fintype.card_pi

end Omega.POM
