import Mathlib.Data.Finset.Sym
import Mathlib.Tactic
import Omega.Conclusion.PartitionPrimesliceDivisibilityValuationPaircount

namespace Omega.Conclusion

/-- Collapse exactly the two vertices `i` and `j` into one block and keep every other vertex in its
own singleton block. -/
def conclusion_partition_primeslice_minimal_uniqueness_edgePartition {n : ℕ} (i j : Fin n) :
    Fin n → Fin (n + 1)
  | x => if x = i then 0 else if x = j then 0 else x.succ

lemma conclusion_partition_primeslice_minimal_uniqueness_edgePartition_collision
    {n : ℕ} {i j x y : Fin n} (_hij : i ≠ j) (hxy : x ≠ y)
    (hlabel :
      conclusion_partition_primeslice_minimal_uniqueness_edgePartition i j x =
        conclusion_partition_primeslice_minimal_uniqueness_edgePartition i j y) :
    (x = i ∧ y = j) ∨ (x = j ∧ y = i) := by
  unfold conclusion_partition_primeslice_minimal_uniqueness_edgePartition at hlabel
  by_cases hx : x = i
  · by_cases hy : y = i
    · exact (hxy (hx.trans hy.symm)).elim
    · by_cases hyj : y = j
      · exact Or.inl ⟨hx, hyj⟩
      · exfalso
        have hzero : (0 : Fin (n + 1)) = y.succ := by
          simpa [hx, hy, hyj] using hlabel
        exact Fin.succ_ne_zero y hzero.symm
  · by_cases hxj : x = j
    · by_cases hy : y = i
      · exact Or.inr ⟨hxj, hy⟩
      · by_cases hyj : y = j
        · exact (hxy (hxj.trans hyj.symm)).elim
        · exfalso
          have hzero : (0 : Fin (n + 1)) = y.succ := by
            simpa [hx, hxj, hy, hyj] using hlabel
          exact Fin.succ_ne_zero y hzero.symm
    · by_cases hy : y = i
      · exfalso
        have hzero : (0 : Fin (n + 1)) = x.succ := by
          simpa [hx, hxj, hy] using hlabel.symm
        exact Fin.succ_ne_zero x hzero.symm
      · by_cases hyj : y = j
        · exfalso
          have hzero : (0 : Fin (n + 1)) = x.succ := by
            simpa [hx, hxj, hy, hyj] using hlabel.symm
          exact Fin.succ_ne_zero x hzero.symm
        · have hsucc : x.succ = y.succ := by
            simpa [hx, hxj, hy, hyj] using hlabel
          have hxy_eq : x = y := by
            exact Fin.ext (by simpa using congrArg Fin.val hsucc)
          exact (hxy hxy_eq).elim

lemma conclusion_partition_primeslice_minimal_uniqueness_singleton_support
    {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    partitionPrimeSupport
        (conclusion_partition_primeslice_minimal_uniqueness_edgePartition i j) =
      {s(i, j)} := by
  ext e
  refine Sym2.inductionOn e ?_
  intro x y
  constructor
  · intro he
    rw [partitionPrimeSupport, Finset.mem_biUnion] at he
    rcases he with ⟨b, -, hb⟩
    rcases mem_blockPairSupport_iff.mp hb with ⟨hpair, hdiag⟩
    have hx :
        x ∈
          blockFiber
            (conclusion_partition_primeslice_minimal_uniqueness_edgePartition i j) b := by
      simpa using (Finset.mem_sym2_iff.mp hpair) x (Sym2.mem_mk_left x y)
    have hy :
        y ∈
          blockFiber
            (conclusion_partition_primeslice_minimal_uniqueness_edgePartition i j) b := by
      simpa using (Finset.mem_sym2_iff.mp hpair) y (Sym2.mem_mk_right x y)
    rw [blockFiber, Finset.mem_filter] at hx hy
    have hxy : x ≠ y := by
      simpa [Sym2.mk_isDiag_iff] using hdiag
    have hlabel :
        conclusion_partition_primeslice_minimal_uniqueness_edgePartition i j x =
          conclusion_partition_primeslice_minimal_uniqueness_edgePartition i j y := by
      exact hx.2.trans hy.2.symm
    rcases conclusion_partition_primeslice_minimal_uniqueness_edgePartition_collision
        hij hxy hlabel with hxy' | hxy'
    · rcases hxy' with ⟨rfl, rfl⟩
      simp
    · rcases hxy' with ⟨rfl, rfl⟩
      simp
  · intro he
    have he' : s(x, y) = s(i, j) := by
      simpa using he
    rcases Sym2.eq_iff.mp he' with hxy' | hxy'
    · rcases hxy' with ⟨rfl, rfl⟩
      rw [partitionPrimeSupport, Finset.mem_biUnion]
      refine ⟨0, by simp, ?_⟩
      refine mem_blockPairSupport_iff.mpr ?_
      refine ⟨?_, by simpa [Sym2.mk_isDiag_iff] using hij⟩
      rw [Finset.mk_mem_sym2_iff]
      constructor <;>
        simp [blockFiber, conclusion_partition_primeslice_minimal_uniqueness_edgePartition, hij]
    · rcases hxy' with ⟨rfl, rfl⟩
      rw [partitionPrimeSupport, Finset.mem_biUnion]
      refine ⟨0, by simp, ?_⟩
      refine mem_blockPairSupport_iff.mpr ?_
      refine ⟨?_, by simpa [Sym2.mk_isDiag_iff] using hij.symm⟩
      rw [Finset.mk_mem_sym2_iff]
      constructor <;>
        simp [blockFiber, conclusion_partition_primeslice_minimal_uniqueness_edgePartition, hij]

/-- Paper label: `thm:conclusion-partition-primeslice-minimal-uniqueness`.
In the current non-diagonal prime-slice signature, the code of every partition determines the
prime label on each non-diagonal atom. -/
theorem paper_conclusion_partition_primeslice_minimal_uniqueness
    {n : ℕ} (E E' : PrimeSliceEncoding n)
    (hcode :
      ∀ π : Fin n → Fin (n + 1),
        partitionPrimeCode E π = partitionPrimeCode E' π) :
    ∀ e : Sym2 (Fin n), ¬ e.IsDiag → E.edgePrime e = E'.edgePrime e := by
  intro e hdiag
  revert hdiag
  refine Sym2.inductionOn e ?_
  intro i j hdiag'
  have hij : i ≠ j := by
    simpa [Sym2.mk_isDiag_iff] using hdiag'
  let π := conclusion_partition_primeslice_minimal_uniqueness_edgePartition i j
  have hsupport :
      partitionPrimeSupport π = {s(i, j)} :=
    conclusion_partition_primeslice_minimal_uniqueness_singleton_support hij
  have hcode_eq := hcode π
  simpa [partitionPrimeCode, hsupport] using hcode_eq

end Omega.Conclusion
