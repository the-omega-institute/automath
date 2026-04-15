import Omega.SPG.PrefixMetric

namespace Omega.SPG

open Set

theorem isOpen_cylinderWord (w : Word m) : IsOpen (cylinderWord w) := by
  rw [cylinderWord_eq_piCylinder]
  exact PiNat.isOpen_cylinder (fun _ : ℕ => Bool) (extendWord w) m

theorem isOpen_fromWordSet (A : Set (Word m)) : IsOpen (fromWordSet A) := by
  rw [fromWordSet_eq_iUnion]
  refine isOpen_iUnion ?_
  intro w
  refine isOpen_iUnion ?_
  intro _hw
  exact isOpen_cylinderWord w

theorem isClopen_fromWordSet (A : Set (Word m)) : IsClopen (fromWordSet A) := by
  refine ⟨?_, isOpen_fromWordSet A⟩
  refine ⟨?_⟩
  simpa [fromWordSet_compl] using isOpen_fromWordSet (A := Aᶜ)

/-- Finite-prefix events are clopen in the product topology. -/
theorem prefixDetermined_isClopen {s : Set OmegaInfinity} (m : Nat)
    (hs : PrefixDetermined s m) : IsClopen s := by
  rcases (prefixDetermined_iff_exists_fromWordSet s m).1 hs with ⟨A, rfl⟩
  exact isClopen_fromWordSet A

/-- The SPG-facing clopen theorem: any event cut out by finitely many prefixes is clopen.
    prop:spg-decidable-clopen -/
theorem spg_decidableClopen (A : Set (Word m)) : IsClopen (fromWordSet A) :=
  isClopen_fromWordSet A

/-- Cylinder sets are clopen. -/
theorem isClopen_cylinderWord (w : Word m) : IsClopen (cylinderWord w) := by
  have := isClopen_fromWordSet {w}
  rwa [show fromWordSet ({w} : Set (Word m)) = cylinderWord w from by ext x; simp [fromWordSet]] at this

/-- The intersection of two clopen fromWordSets is a clopen fromWordSet. -/
theorem isClopen_fromWordSet_inter (A B : Set (Word m)) :
    IsClopen (fromWordSet A ∩ fromWordSet B) := by
  rw [← fromWordSet_inter]; exact isClopen_fromWordSet (A ∩ B)

/-- The union of two clopen fromWordSets is a clopen fromWordSet. -/
theorem isClopen_fromWordSet_union (A B : Set (Word m)) :
    IsClopen (fromWordSet A ∪ fromWordSet B) := by
  rw [← fromWordSet_union]; exact isClopen_fromWordSet (A ∪ B)

/-- The complement of a fromWordSet is clopen. -/
theorem isClopen_fromWordSet_compl (A : Set (Word m)) :
    IsClopen (fromWordSet A)ᶜ := by
  rw [fromWordSet_compl]; exact isClopen_fromWordSet Aᶜ

/-- Finite intersections of cylinders are clopen. -/
theorem isClopen_finite_inter_cylinders {S : Finset (Word m)}
    (A : Set (Word m)) (_hA : A = ↑S) :
    IsClopen (fromWordSet A) :=
  isClopen_fromWordSet A

/-- The complement of a clopen fromWordSet is also a clopen fromWordSet. -/
theorem fromWordSet_compl_is_clopen (A : Set (Word m)) :
    IsClopen (fromWordSet Aᶜ) :=
  isClopen_fromWordSet Aᶜ

/-- Empty set is clopen (as fromWordSet of empty). -/
theorem isClopen_empty_spg : IsClopen (∅ : Set OmegaInfinity) := by
  rw [show (∅ : Set OmegaInfinity) = fromWordSet (∅ : Set (Word 0)) from by simp]
  exact isClopen_fromWordSet ∅

-- ══════════════════════════════════════════════════════════════
-- Phase R307: SPG clopen diff/symmDiff
-- ══════════════════════════════════════════════════════════════

/-- def:spg-prefix-event -/
theorem isClopen_fromWordSet_diff (A B : Set (Word m)) :
    IsClopen (fromWordSet A \ fromWordSet B) := by
  rw [Set.diff_eq]
  exact (isClopen_fromWordSet A).inter (isClopen_fromWordSet B).compl

/-- def:spg-prefix-event -/
theorem isClopen_fromWordSet_symmDiff (A B : Set (Word m)) :
    IsClopen (symmDiff (fromWordSet A) (fromWordSet B)) := by
  rw [Set.symmDiff_def]
  exact (isClopen_fromWordSet_diff A B).union (isClopen_fromWordSet_diff B A)

/-- Paper package. def:spg-prefix-event -/
theorem paper_spg_prefix_boolean :
    (∀ A B : Set (Word m), IsClopen (fromWordSet A \ fromWordSet B)) ∧
    (∀ A B : Set (Word m), IsClopen (symmDiff (fromWordSet A) (fromWordSet B))) :=
  ⟨isClopen_fromWordSet_diff, isClopen_fromWordSet_symmDiff⟩

/-- The full space Ω∞ is clopen.
    prop:spg-decidable-clopen -/
theorem isClopen_univ_spg : IsClopen (Set.univ : Set OmegaInfinity) := by
  rw [show (Set.univ : Set OmegaInfinity) = fromWordSet (Set.univ : Set (Word 0)) from
    (fromWordSet_univ).symm]
  exact isClopen_fromWordSet Set.univ

/-- Triple intersection of clopen fromWordSets.
    def:spg-prefix-event -/
theorem isClopen_fromWordSet_triple_inter (A B C : Set (Word m)) :
    IsClopen (fromWordSet A ∩ fromWordSet B ∩ fromWordSet C) :=
  (isClopen_fromWordSet_inter A B).inter (isClopen_fromWordSet C)

/-- de Morgan: complement of intersection is clopen.
    def:spg-prefix-event -/
theorem isClopen_fromWordSet_inter_compl (A B : Set (Word m)) :
    IsClopen ((fromWordSet A ∩ fromWordSet B)ᶜ) :=
  (isClopen_fromWordSet_inter A B).compl

/-- de Morgan: complement of union is clopen.
    def:spg-prefix-event -/
theorem isClopen_fromWordSet_union_compl (A B : Set (Word m)) :
    IsClopen ((fromWordSet A ∪ fromWordSet B)ᶜ) :=
  (isClopen_fromWordSet_union A B).compl

/-- Extended paper package: universal clopen, triple intersection, de Morgan complements.
    def:spg-prefix-event / prop:spg-decidable-clopen -/
theorem paper_spg_prefix_boolean_extended :
    IsClopen (Set.univ : Set OmegaInfinity) ∧
    (∀ A B C : Set (Word m),
      IsClopen (fromWordSet A ∩ fromWordSet B ∩ fromWordSet C)) ∧
    (∀ A B : Set (Word m), IsClopen ((fromWordSet A ∩ fromWordSet B)ᶜ)) ∧
    (∀ A B : Set (Word m), IsClopen ((fromWordSet A ∪ fromWordSet B)ᶜ)) :=
  ⟨isClopen_univ_spg,
   isClopen_fromWordSet_triple_inter,
   isClopen_fromWordSet_inter_compl,
   isClopen_fromWordSet_union_compl⟩

end Omega.SPG
