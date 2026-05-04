import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete finite atom/depth package for the finite-defect depth flag. -/
structure conclusion_finite_defect_depth_jordan_holder_flag_data where
  conclusion_finite_defect_depth_jordan_holder_flag_atoms : Finset ℕ
  conclusion_finite_defect_depth_jordan_holder_flag_depth : ℕ → ℕ
  conclusion_finite_defect_depth_jordan_holder_flag_depths : List ℕ
  conclusion_finite_defect_depth_jordan_holder_flag_depths_nodup :
    conclusion_finite_defect_depth_jordan_holder_flag_depths.Nodup
  conclusion_finite_defect_depth_jordan_holder_flag_depths_complete :
    ∀ a,
      a ∈ conclusion_finite_defect_depth_jordan_holder_flag_atoms →
        conclusion_finite_defect_depth_jordan_holder_flag_depth a ∈
          conclusion_finite_defect_depth_jordan_holder_flag_depths
  conclusion_finite_defect_depth_jordan_holder_flag_depths_sound :
    ∀ d,
      d ∈ conclusion_finite_defect_depth_jordan_holder_flag_depths →
        ∃ a ∈ conclusion_finite_defect_depth_jordan_holder_flag_atoms,
          conclusion_finite_defect_depth_jordan_holder_flag_depth a = d

/-- Cumulative layer obtained by keeping atoms whose depth occurs in the first `i` depth slots. -/
def conclusion_finite_defect_depth_jordan_holder_flag_layer
    (D : conclusion_finite_defect_depth_jordan_holder_flag_data) (i : ℕ) : Finset ℕ :=
  D.conclusion_finite_defect_depth_jordan_holder_flag_atoms.filter fun a =>
    D.conclusion_finite_defect_depth_jordan_holder_flag_depth a ∈
      D.conclusion_finite_defect_depth_jordan_holder_flag_depths.take i

/-- The atoms living exactly at one displayed depth. -/
def conclusion_finite_defect_depth_jordan_holder_flag_depth_layer
    (D : conclusion_finite_defect_depth_jordan_holder_flag_data) (d : ℕ) : Finset ℕ :=
  D.conclusion_finite_defect_depth_jordan_holder_flag_atoms.filter fun a =>
    D.conclusion_finite_defect_depth_jordan_holder_flag_depth a = d

/-- The new layer added at the `i`th depth slot. -/
def conclusion_finite_defect_depth_jordan_holder_flag_layer_difference
    (D : conclusion_finite_defect_depth_jordan_holder_flag_data) (i : ℕ) : Finset ℕ :=
  conclusion_finite_defect_depth_jordan_holder_flag_layer D (i + 1) \
    conclusion_finite_defect_depth_jordan_holder_flag_layer D i

lemma conclusion_finite_defect_depth_jordan_holder_flag_mem_new_depth
    (D : conclusion_finite_defect_depth_jordan_holder_flag_data) {i d : ℕ}
    (hi : i < D.conclusion_finite_defect_depth_jordan_holder_flag_depths.length) :
    d ∈ D.conclusion_finite_defect_depth_jordan_holder_flag_depths.take (i + 1) ∧
        d ∉ D.conclusion_finite_defect_depth_jordan_holder_flag_depths.take i ↔
      d = D.conclusion_finite_defect_depth_jordan_holder_flag_depths[i] := by
  let depths := D.conclusion_finite_defect_depth_jordan_holder_flag_depths
  have htake : depths.take (i + 1) = depths.take i ++ [depths[i]] := by
    simp [List.take_concat_get' depths i hi]
  constructor
  · rintro ⟨hmem, hnotmem⟩
    rw [htake] at hmem
    rcases List.mem_append.mp hmem with hleft | hright
    · exact False.elim (hnotmem hleft)
    · simpa using hright
  · intro hd
    subst d
    constructor
    · have hmem : depths[i] ∈ depths.take (i + 1) := by
        rw [htake]
        exact List.mem_append.mpr (Or.inr (by simp))
      simpa [depths] using hmem
    · intro hmem
      have hmem_depths : depths[i] ∈ depths := List.mem_of_mem_take hmem
      have hidx :
          depths.idxOf depths[i] = i :=
        D.conclusion_finite_defect_depth_jordan_holder_flag_depths_nodup.idxOf_getElem i hi
      have hlt : depths.idxOf depths[i] < i :=
        (List.mem_take_iff_idxOf_lt hmem_depths).1 hmem
      omega

/-- Paper-facing finite-defect depth flag statement. -/
def conclusion_finite_defect_depth_jordan_holder_flag_statement
    (D : conclusion_finite_defect_depth_jordan_holder_flag_data) : Prop :=
  conclusion_finite_defect_depth_jordan_holder_flag_layer D 0 = ∅ ∧
    conclusion_finite_defect_depth_jordan_holder_flag_layer D
        D.conclusion_finite_defect_depth_jordan_holder_flag_depths.length =
      D.conclusion_finite_defect_depth_jordan_holder_flag_atoms ∧
    (∀ i,
      i < D.conclusion_finite_defect_depth_jordan_holder_flag_depths.length →
        conclusion_finite_defect_depth_jordan_holder_flag_layer D i ⊂
          conclusion_finite_defect_depth_jordan_holder_flag_layer D (i + 1)) ∧
    ∀ i (hi : i < D.conclusion_finite_defect_depth_jordan_holder_flag_depths.length),
        conclusion_finite_defect_depth_jordan_holder_flag_layer_difference D i =
          conclusion_finite_defect_depth_jordan_holder_flag_depth_layer D
            (D.conclusion_finite_defect_depth_jordan_holder_flag_depths.get ⟨i, hi⟩)

/-- Paper label: `thm:conclusion-finite-defect-depth-jordan-holder-flag`. -/
theorem paper_conclusion_finite_defect_depth_jordan_holder_flag
    (D : conclusion_finite_defect_depth_jordan_holder_flag_data) :
    conclusion_finite_defect_depth_jordan_holder_flag_statement D := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext a
    simp [conclusion_finite_defect_depth_jordan_holder_flag_layer]
  · ext a
    constructor
    · intro ha
      exact (Finset.mem_filter.mp ha).1
    · intro ha
      exact Finset.mem_filter.mpr ⟨ha,
        by simpa using D.conclusion_finite_defect_depth_jordan_holder_flag_depths_complete a ha⟩
  · intro i hi
    constructor
    · intro a ha
      rcases Finset.mem_filter.mp ha with ⟨ha_atom, ha_depth⟩
      exact Finset.mem_filter.mpr ⟨ha_atom, by
        have hmem_depths :
            D.conclusion_finite_defect_depth_jordan_holder_flag_depth a ∈
              D.conclusion_finite_defect_depth_jordan_holder_flag_depths :=
          List.mem_of_mem_take ha_depth
        have hidx :
            D.conclusion_finite_defect_depth_jordan_holder_flag_depths.idxOf
                (D.conclusion_finite_defect_depth_jordan_holder_flag_depth a) < i :=
          (List.mem_take_iff_idxOf_lt hmem_depths).1 ha_depth
        exact (List.mem_take_iff_idxOf_lt hmem_depths).2 (Nat.lt_succ_of_lt hidx)⟩
    · intro heq
      obtain ⟨a, ha_atom, ha_depth⟩ :=
        D.conclusion_finite_defect_depth_jordan_holder_flag_depths_sound
          (D.conclusion_finite_defect_depth_jordan_holder_flag_depths.get ⟨i, hi⟩) (by
            exact List.get_mem _ _)
      have ha_next :
          a ∈ conclusion_finite_defect_depth_jordan_holder_flag_layer D (i + 1) := by
        exact Finset.mem_filter.mpr ⟨ha_atom, by
          have hnew :=
            (conclusion_finite_defect_depth_jordan_holder_flag_mem_new_depth D hi
              (d := D.conclusion_finite_defect_depth_jordan_holder_flag_depths.get ⟨i, hi⟩)).2 rfl
          simpa [ha_depth] using hnew.1⟩
      have ha_current :
          a ∉ conclusion_finite_defect_depth_jordan_holder_flag_layer D i := by
        intro ha
        rcases Finset.mem_filter.mp ha with ⟨_, hmem⟩
        have hnew :=
          (conclusion_finite_defect_depth_jordan_holder_flag_mem_new_depth D hi
            (d := D.conclusion_finite_defect_depth_jordan_holder_flag_depths.get ⟨i, hi⟩)).2 rfl
        exact hnew.2 (by simpa [ha_depth] using hmem)
      exact ha_current (heq ha_next)
  · intro i hi
    ext a
    constructor
    · intro ha
      rcases Finset.mem_sdiff.mp ha with ⟨ha_next, ha_not_current⟩
      rcases Finset.mem_filter.mp ha_next with ⟨ha_atom, ha_depth_next⟩
      have ha_depth_not_current :
          D.conclusion_finite_defect_depth_jordan_holder_flag_depth a ∉
            D.conclusion_finite_defect_depth_jordan_holder_flag_depths.take i := by
        intro hmem
        exact ha_not_current (Finset.mem_filter.mpr ⟨ha_atom, hmem⟩)
      have hdepth :=
        (conclusion_finite_defect_depth_jordan_holder_flag_mem_new_depth D hi).1
          ⟨ha_depth_next, ha_depth_not_current⟩
      exact Finset.mem_filter.mpr ⟨ha_atom, hdepth⟩
    · intro ha
      rcases Finset.mem_filter.mp ha with ⟨ha_atom, ha_depth⟩
      rw [conclusion_finite_defect_depth_jordan_holder_flag_layer_difference]
      refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨ha_atom, by
          have hnew :=
            (conclusion_finite_defect_depth_jordan_holder_flag_mem_new_depth D hi
              (d := D.conclusion_finite_defect_depth_jordan_holder_flag_depths.get ⟨i, hi⟩)).2 rfl
          simpa [ha_depth] using hnew.1⟩
      · intro ha_current
        rcases Finset.mem_filter.mp ha_current with ⟨_, hmem⟩
        have hnew :=
          (conclusion_finite_defect_depth_jordan_holder_flag_mem_new_depth D hi
            (d := D.conclusion_finite_defect_depth_jordan_holder_flag_depths.get ⟨i, hi⟩)).2 rfl
        exact hnew.2 (by simpa [ha_depth] using hmem)

end Omega.Conclusion
