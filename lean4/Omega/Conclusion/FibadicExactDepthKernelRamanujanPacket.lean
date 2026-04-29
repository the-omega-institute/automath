import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Concrete finite exact-depth character packet for the fibadic Ramanujan-kernel formula. -/
structure conclusion_fibadic_exact_depth_kernel_ramanujan_packet_Data where
  conclusion_fibadic_exact_depth_kernel_ramanujan_packet_Character : Type
  conclusion_fibadic_exact_depth_kernel_ramanujan_packet_fintype :
    Fintype conclusion_fibadic_exact_depth_kernel_ramanujan_packet_Character
  conclusion_fibadic_exact_depth_kernel_ramanujan_packet_decidableEq :
    DecidableEq conclusion_fibadic_exact_depth_kernel_ramanujan_packet_Character
  conclusion_fibadic_exact_depth_kernel_ramanujan_packet_depth :
    conclusion_fibadic_exact_depth_kernel_ramanujan_packet_Character → ℕ
  conclusion_fibadic_exact_depth_kernel_ramanujan_packet_maxDepth : ℕ
  conclusion_fibadic_exact_depth_kernel_ramanujan_packet_depth_le_max :
    ∀ χ,
      conclusion_fibadic_exact_depth_kernel_ramanujan_packet_depth χ ≤
        conclusion_fibadic_exact_depth_kernel_ramanujan_packet_maxDepth
  conclusion_fibadic_exact_depth_kernel_ramanujan_packet_primitiveValue :
    conclusion_fibadic_exact_depth_kernel_ramanujan_packet_Character → ℤ

attribute [instance]
  conclusion_fibadic_exact_depth_kernel_ramanujan_packet_Data.conclusion_fibadic_exact_depth_kernel_ramanujan_packet_fintype
  conclusion_fibadic_exact_depth_kernel_ramanujan_packet_Data.conclusion_fibadic_exact_depth_kernel_ramanujan_packet_decidableEq

namespace conclusion_fibadic_exact_depth_kernel_ramanujan_packet_Data

/-- The finite packet of primitive characters whose exact fibadic depth is `d`. -/
def conclusion_fibadic_exact_depth_kernel_ramanujan_packet_exactDepthPacket
    (D : conclusion_fibadic_exact_depth_kernel_ramanujan_packet_Data) (d : ℕ) :
    Finset D.conclusion_fibadic_exact_depth_kernel_ramanujan_packet_Character :=
  Finset.univ.filter
    (fun χ => D.conclusion_fibadic_exact_depth_kernel_ramanujan_packet_depth χ = d)

/-- Grouped primitive character sum at exact depth `d`. -/
def conclusion_fibadic_exact_depth_kernel_ramanujan_packet_groupedPrimitiveSum
    (D : conclusion_fibadic_exact_depth_kernel_ramanujan_packet_Data) (d : ℕ) : ℤ :=
  ∑ χ ∈ D.conclusion_fibadic_exact_depth_kernel_ramanujan_packet_exactDepthPacket d,
    D.conclusion_fibadic_exact_depth_kernel_ramanujan_packet_primitiveValue χ

/-- The exact-depth kernel, written as the grouped primitive character sum. -/
def conclusion_fibadic_exact_depth_kernel_ramanujan_packet_kernel
    (D : conclusion_fibadic_exact_depth_kernel_ramanujan_packet_Data) (d : ℕ) : ℤ :=
  D.conclusion_fibadic_exact_depth_kernel_ramanujan_packet_groupedPrimitiveSum d

/-- The Ramanujan packet formula expands the kernel by grouping primitive characters of depth `d`. -/
def ramanujanPacketFormula
    (D : conclusion_fibadic_exact_depth_kernel_ramanujan_packet_Data) : Prop :=
  ∀ d : ℕ,
    D.conclusion_fibadic_exact_depth_kernel_ramanujan_packet_kernel d =
      D.conclusion_fibadic_exact_depth_kernel_ramanujan_packet_groupedPrimitiveSum d

/-- Finite support of exact depths gives a quotient through the finite depth ledger. -/
def factorsThroughFiniteQuotient
    (D : conclusion_fibadic_exact_depth_kernel_ramanujan_packet_Data) : Prop :=
  Finset.univ =
    (Finset.range (D.conclusion_fibadic_exact_depth_kernel_ramanujan_packet_maxDepth + 1)).biUnion
      (fun d => D.conclusion_fibadic_exact_depth_kernel_ramanujan_packet_exactDepthPacket d)

/-- Exact-depth packets of distinct depths are disjoint. -/
def depthOrthogonality
    (D : conclusion_fibadic_exact_depth_kernel_ramanujan_packet_Data) : Prop :=
  ∀ d e : ℕ, d ≠ e →
    Disjoint
      (D.conclusion_fibadic_exact_depth_kernel_ramanujan_packet_exactDepthPacket d)
      (D.conclusion_fibadic_exact_depth_kernel_ramanujan_packet_exactDepthPacket e)

/-- There is no primitive mass at the first depth beyond the finite support. -/
def zeroValueMass
    (D : conclusion_fibadic_exact_depth_kernel_ramanujan_packet_Data) : Prop :=
  D.conclusion_fibadic_exact_depth_kernel_ramanujan_packet_kernel
      (D.conclusion_fibadic_exact_depth_kernel_ramanujan_packet_maxDepth + 1) = 0

lemma conclusion_fibadic_exact_depth_kernel_ramanujan_packet_factorsThroughFiniteQuotient
    (D : conclusion_fibadic_exact_depth_kernel_ramanujan_packet_Data) :
    D.factorsThroughFiniteQuotient := by
  classical
  ext χ
  constructor
  · intro _hχ
    refine Finset.mem_biUnion.mpr ?_
    refine
      ⟨D.conclusion_fibadic_exact_depth_kernel_ramanujan_packet_depth χ, ?_, ?_⟩
    · exact Finset.mem_range.mpr
        (Nat.lt_succ_of_le
          (D.conclusion_fibadic_exact_depth_kernel_ramanujan_packet_depth_le_max χ))
    · simp [conclusion_fibadic_exact_depth_kernel_ramanujan_packet_exactDepthPacket]
  · intro _hχ
    simp

lemma conclusion_fibadic_exact_depth_kernel_ramanujan_packet_depthOrthogonality
    (D : conclusion_fibadic_exact_depth_kernel_ramanujan_packet_Data) :
    D.depthOrthogonality := by
  classical
  intro d e hde
  rw [Finset.disjoint_left]
  intro χ hχd hχe
  simp [conclusion_fibadic_exact_depth_kernel_ramanujan_packet_exactDepthPacket] at hχd hχe
  exact hde (hχd.symm.trans hχe)

lemma conclusion_fibadic_exact_depth_kernel_ramanujan_packet_zeroValueMass
    (D : conclusion_fibadic_exact_depth_kernel_ramanujan_packet_Data) : D.zeroValueMass := by
  classical
  unfold zeroValueMass
  unfold conclusion_fibadic_exact_depth_kernel_ramanujan_packet_kernel
  unfold conclusion_fibadic_exact_depth_kernel_ramanujan_packet_groupedPrimitiveSum
  apply Finset.sum_eq_zero
  intro χ hχ
  simp [conclusion_fibadic_exact_depth_kernel_ramanujan_packet_exactDepthPacket] at hχ
  have hle := D.conclusion_fibadic_exact_depth_kernel_ramanujan_packet_depth_le_max χ
  exfalso
  omega

end conclusion_fibadic_exact_depth_kernel_ramanujan_packet_Data

/-- Paper label: `thm:conclusion-fibadic-exact-depth-kernel-ramanujan-packet`. -/
theorem paper_conclusion_fibadic_exact_depth_kernel_ramanujan_packet
    (D : conclusion_fibadic_exact_depth_kernel_ramanujan_packet_Data) :
    D.ramanujanPacketFormula ∧ D.factorsThroughFiniteQuotient ∧ D.depthOrthogonality ∧
      D.zeroValueMass := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro d
    rfl
  · exact D.conclusion_fibadic_exact_depth_kernel_ramanujan_packet_factorsThroughFiniteQuotient
  · exact D.conclusion_fibadic_exact_depth_kernel_ramanujan_packet_depthOrthogonality
  · exact D.conclusion_fibadic_exact_depth_kernel_ramanujan_packet_zeroValueMass

end Omega.Conclusion
