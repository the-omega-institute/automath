import Mathlib.Tactic

namespace Omega.POM

/-- A face of the disjoint-union independence complex is a finite set supported on the component
union whose restriction to each component is a face of the corresponding component complex. -/
def pom_independence_complex_join_componentwise_face
    {α ι : Type*} [DecidableEq α] [Fintype ι] [DecidableEq ι]
    (components : ι → Finset α) (faces : ι → Set (Finset α)) (s : Finset α) : Prop :=
  s ⊆ Finset.biUnion Finset.univ components ∧ ∀ i, s ∩ components i ∈ faces i

/-- A face of the iterated simplicial join is given by choosing one face in each component
complex, requiring pairwise disjoint supports, and taking the union. -/
def pom_independence_complex_join_iterated_face
    {α ι : Type*} [DecidableEq α] [Fintype ι] [DecidableEq ι]
    (faces : ι → Set (Finset α)) (s : Finset α) : Prop :=
  ∃ t : ι → Finset α,
    (∀ i, t i ∈ faces i) ∧
      Pairwise (fun i j => Disjoint (t i) (t j)) ∧
      Finset.biUnion Finset.univ t = s

/-- Paper label: `lem:pom-independence-complex-join`.
For a pairwise-disjoint finite family of components, the componentwise face description of the
disjoint-union independence complex is equivalent to the finite simplicial-join face description.
-/
theorem paper_pom_independence_complex_join
    {α ι : Type*} [DecidableEq α] [Fintype ι] [DecidableEq ι]
    (components : ι → Finset α) (faces : ι → Set (Finset α))
    (hdisj : Pairwise fun i j => Disjoint (components i) (components j))
    (hfaces : ∀ i t, t ∈ faces i → t ⊆ components i) (s : Finset α) :
    pom_independence_complex_join_componentwise_face components faces s ↔
      pom_independence_complex_join_iterated_face faces s := by
  constructor
  · rintro ⟨hsub, hsfaces⟩
    refine ⟨fun i => s ∩ components i, hsfaces, ?_, ?_⟩
    · intro i j hij
      refine Finset.disjoint_left.mpr ?_
      intro x hxi hxj
      exact (Finset.disjoint_left.mp (hdisj hij)) (Finset.mem_inter.mp hxi).2 (Finset.mem_inter.mp hxj).2
    · ext x
      constructor
      · intro hx
        rcases Finset.mem_biUnion.mp hx with ⟨i, -, hxi⟩
        exact (Finset.mem_inter.mp hxi).1
      · intro hx
        have hxUnion : x ∈ Finset.biUnion Finset.univ components := hsub hx
        rcases Finset.mem_biUnion.mp hxUnion with ⟨i, -, hxi⟩
        exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, Finset.mem_inter.mpr ⟨hx, hxi⟩⟩
  · rintro ⟨t, htfaces, hpairwise, hUnion⟩
    refine ⟨?_, ?_⟩
    · intro x hx
      have hxUnion : x ∈ Finset.biUnion Finset.univ t := by simpa [hUnion] using hx
      rcases Finset.mem_biUnion.mp hxUnion with ⟨i, -, hxi⟩
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hfaces i (t i) (htfaces i) hxi⟩
    · intro i
      have hsubset_i : t i ⊆ components i := hfaces i (t i) (htfaces i)
      have hinter :
          s ∩ components i = t i := by
        ext x
        constructor
        · intro hx
          have hsx : x ∈ s := (Finset.mem_inter.mp hx).1
          have hxcomp : x ∈ components i := (Finset.mem_inter.mp hx).2
          have hxUnion : x ∈ Finset.biUnion Finset.univ t := by simpa [hUnion] using hsx
          rcases Finset.mem_biUnion.mp hxUnion with ⟨j, -, hxj⟩
          by_cases hij : j = i
          · simpa [hij] using hxj
          · exact False.elim ((Finset.disjoint_left.mp (hdisj hij)) (hfaces j (t j) (htfaces j) hxj) hxcomp)
        · intro hx
          have hsx : x ∈ s := by
            have hxUnion : x ∈ Finset.biUnion Finset.univ t :=
              Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hx⟩
            simpa [hUnion] using hxUnion
          exact Finset.mem_inter.mpr ⟨hsx, hsubset_i hx⟩
      simpa [hinter] using htfaces i

end Omega.POM
