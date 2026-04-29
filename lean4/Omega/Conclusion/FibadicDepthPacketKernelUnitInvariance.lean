import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.FinRange

namespace Omega.Conclusion

open scoped BigOperators

/-- Concrete finite data for the fibadic depth-packet unit-invariance theorem. Each depth layer
contributes one finite packet kernel on the residue representatives `Fin modulus`, and
`unitAction` is the permutation induced by multiplication by a fixed unit modulo the same modulus.
-/
structure conclusion_fibadic_depth_packet_kernel_unit_invariance_data where
  modulus : ℕ
  depth : ℕ
  paper_label_conclusion_fibadic_depth_packet_kernel_unit_invariance_coeff : Fin depth → ℂ
  paper_label_conclusion_fibadic_depth_packet_kernel_unit_invariance_kernel :
    Fin depth → Fin modulus → ℂ
  paper_label_conclusion_fibadic_depth_packet_kernel_unit_invariance_unitAction :
    Equiv.Perm (Fin modulus)

namespace conclusion_fibadic_depth_packet_kernel_unit_invariance_data

instance (D : conclusion_fibadic_depth_packet_kernel_unit_invariance_data) :
    Fintype (Fin D.modulus) where
  elems := (List.finRange D.modulus).toFinset
  complete := by
    intro x
    simp

instance (D : conclusion_fibadic_depth_packet_kernel_unit_invariance_data) :
    Fintype (Fin D.depth) where
  elems := (List.finRange D.depth).toFinset
  complete := by
    intro x
    simp

/-- The kernel sum attached to one depth layer. -/
def paper_label_conclusion_fibadic_depth_packet_kernel_unit_invariance_component
    (D : conclusion_fibadic_depth_packet_kernel_unit_invariance_data) (i : Fin D.depth) : ℂ :=
  ∑ x : Fin D.modulus, D.paper_label_conclusion_fibadic_depth_packet_kernel_unit_invariance_kernel i x

/-- The same depth component after twisting the residue system by the fixed unit permutation. -/
def paper_label_conclusion_fibadic_depth_packet_kernel_unit_invariance_twistedComponent
    (D : conclusion_fibadic_depth_packet_kernel_unit_invariance_data) (i : Fin D.depth) : ℂ :=
  ∑ x : Fin D.modulus,
    D.paper_label_conclusion_fibadic_depth_packet_kernel_unit_invariance_kernel i
      (D.paper_label_conclusion_fibadic_depth_packet_kernel_unit_invariance_unitAction x)

/-- The full finite depth packet. -/
def paper_label_conclusion_fibadic_depth_packet_kernel_unit_invariance_packet
    (D : conclusion_fibadic_depth_packet_kernel_unit_invariance_data) : ℂ :=
  ∑ i : Fin D.depth,
    D.paper_label_conclusion_fibadic_depth_packet_kernel_unit_invariance_coeff i *
      D.paper_label_conclusion_fibadic_depth_packet_kernel_unit_invariance_component i

/-- The packet after twisting every kernel layer by the fixed unit action. -/
def paper_label_conclusion_fibadic_depth_packet_kernel_unit_invariance_twistedPacket
    (D : conclusion_fibadic_depth_packet_kernel_unit_invariance_data) : ℂ :=
  ∑ i : Fin D.depth,
    D.paper_label_conclusion_fibadic_depth_packet_kernel_unit_invariance_coeff i *
      D.paper_label_conclusion_fibadic_depth_packet_kernel_unit_invariance_twistedComponent i

/-- Paper-facing formulation: every depth component is invariant under the unit permutation, hence
the whole finite packet is invariant as well. -/
def conclusion_fibadic_depth_packet_kernel_unit_invariance_statement
    (D : conclusion_fibadic_depth_packet_kernel_unit_invariance_data) : Prop :=
  (∀ i,
      D.paper_label_conclusion_fibadic_depth_packet_kernel_unit_invariance_twistedComponent i =
        D.paper_label_conclusion_fibadic_depth_packet_kernel_unit_invariance_component i) ∧
    D.paper_label_conclusion_fibadic_depth_packet_kernel_unit_invariance_twistedPacket =
      D.paper_label_conclusion_fibadic_depth_packet_kernel_unit_invariance_packet

lemma paper_label_conclusion_fibadic_depth_packet_kernel_unit_invariance_component_eq
    (D : conclusion_fibadic_depth_packet_kernel_unit_invariance_data) (i : Fin D.depth) :
    D.paper_label_conclusion_fibadic_depth_packet_kernel_unit_invariance_twistedComponent i =
      D.paper_label_conclusion_fibadic_depth_packet_kernel_unit_invariance_component i := by
  unfold
    paper_label_conclusion_fibadic_depth_packet_kernel_unit_invariance_twistedComponent
    paper_label_conclusion_fibadic_depth_packet_kernel_unit_invariance_component
  refine Fintype.sum_equiv
    D.paper_label_conclusion_fibadic_depth_packet_kernel_unit_invariance_unitAction _ _
    (fun x => rfl)

end conclusion_fibadic_depth_packet_kernel_unit_invariance_data

open conclusion_fibadic_depth_packet_kernel_unit_invariance_data

/-- Paper label: `thm:conclusion-fibadic-depth-packet-kernel-unit-invariance`. The unit action is
a permutation of the finite residue system, so each packet layer and hence the whole fibadic depth
packet are invariant under this transport. -/
theorem paper_conclusion_fibadic_depth_packet_kernel_unit_invariance
    (D : conclusion_fibadic_depth_packet_kernel_unit_invariance_data) :
    D.conclusion_fibadic_depth_packet_kernel_unit_invariance_statement := by
  refine ⟨?_, ?_⟩
  · intro i
    exact D.paper_label_conclusion_fibadic_depth_packet_kernel_unit_invariance_component_eq i
  · unfold
      paper_label_conclusion_fibadic_depth_packet_kernel_unit_invariance_twistedPacket
      paper_label_conclusion_fibadic_depth_packet_kernel_unit_invariance_packet
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [D.paper_label_conclusion_fibadic_depth_packet_kernel_unit_invariance_component_eq i]

end Omega.Conclusion
