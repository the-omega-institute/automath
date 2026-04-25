import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

namespace Omega.POM

/-- Finite words over a finite alphabet, used as the concrete output language for the RMOM
soundness package. -/
abbrev pom_rmom_sound_word (alphabetSize wordLength : ℕ) := Fin wordLength → Fin alphabetSize

instance pom_rmom_sound_word_decidableEq (alphabetSize wordLength : ℕ) :
    DecidableEq (pom_rmom_sound_word alphabetSize wordLength) := by
  infer_instance

/-- Concrete finite-language data for the RMOM soundness statement. -/
structure pom_rmom_sound_data where
  alphabetSize : ℕ
  wordLength : ℕ
  p : ℕ
  q : ℕ
  language : pom_rmom_sound_word alphabetSize wordLength → Prop
  language_decidable : DecidablePred language

attribute [instance] pom_rmom_sound_data.language_decidable

/-- The grouped `p`-by-`q` indexing for the iterated moment compiler. -/
abbrev pom_rmom_sound_grouped_index (D : pom_rmom_sound_data) := Fin D.p × Fin D.q

/-- The flat `pq`-fold indexing for the one-shot moment compiler. -/
abbrev pom_rmom_sound_flat_index (D : pom_rmom_sound_data) := Fin (D.p * D.q)

/-- Grouped collision tuples indexed by `Fin p × Fin q`. -/
abbrev pom_rmom_sound_grouped_tuple (D : pom_rmom_sound_data) :=
  pom_rmom_sound_grouped_index D → pom_rmom_sound_word D.alphabetSize D.wordLength

/-- Flat collision tuples indexed by `Fin (p*q)`. -/
abbrev pom_rmom_sound_flat_tuple (D : pom_rmom_sound_data) :=
  pom_rmom_sound_flat_index D → pom_rmom_sound_word D.alphabetSize D.wordLength

instance pom_rmom_sound_grouped_tuple_decidableEq (D : pom_rmom_sound_data) :
    DecidableEq (pom_rmom_sound_grouped_tuple D) := by
  infer_instance

instance pom_rmom_sound_flat_tuple_decidableEq (D : pom_rmom_sound_data) :
    DecidableEq (pom_rmom_sound_flat_tuple D) := by
  infer_instance

/-- The grouped `p`-then-`q` collision data: every slot lies in the language and all slots are
synchronized. -/
def pom_rmom_sound_grouped_collision_tuple (D : pom_rmom_sound_data) :=
  {f : pom_rmom_sound_grouped_tuple D // (∀ x, D.language (f x)) ∧ ∀ x y, f x = f y}

/-- The flat `pq`-fold collision data: every slot lies in the language and all slots are
synchronized. -/
def pom_rmom_sound_flat_collision_tuple (D : pom_rmom_sound_data) :=
  {f : pom_rmom_sound_flat_tuple D // (∀ x, D.language (f x)) ∧ ∀ x y, f x = f y}

/-- Reindex grouped tuples by flattening `Fin p × Fin q` to `Fin (p*q)`. -/
def pom_rmom_sound_grouped_flat_equiv (D : pom_rmom_sound_data) :
    pom_rmom_sound_grouped_tuple D ≃ pom_rmom_sound_flat_tuple D :=
  Equiv.arrowCongr finProdFinEquiv (Equiv.refl _)

/-- The grouped and flat synchronized collision tuples are in bijection. -/
def pom_rmom_sound_collision_tuple_equiv (D : pom_rmom_sound_data) :
    pom_rmom_sound_grouped_collision_tuple D ≃ pom_rmom_sound_flat_collision_tuple D where
  toFun x :=
    ⟨pom_rmom_sound_grouped_flat_equiv D x.1, by
      constructor
      · intro y
        exact x.2.1 (finProdFinEquiv.symm y)
      · intro y z
        exact x.2.2 (finProdFinEquiv.symm y) (finProdFinEquiv.symm z)⟩
  invFun x :=
    ⟨(pom_rmom_sound_grouped_flat_equiv D).symm x.1, by
      constructor
      · intro y
        exact x.2.1 (finProdFinEquiv y)
      · intro y z
        exact x.2.2 (finProdFinEquiv y) (finProdFinEquiv z)⟩
  left_inv x := by
    apply Subtype.ext
    funext y
    simpa using congrArg x.1 (finProdFinEquiv.left_inv y)
  right_inv x := by
    apply Subtype.ext
    funext y
    simpa using congrArg x.1 (finProdFinEquiv.right_inv y)

/-- The embedding from the filtered grouped tuple enumeration to the grouped collision subtype. -/
def pom_rmom_sound_grouped_collision_tuple_embedding (D : pom_rmom_sound_data) :
    {f // f ∈ Finset.univ.filter fun g : pom_rmom_sound_grouped_tuple D =>
      (∀ x, D.language (g x)) ∧ ∀ x y, g x = g y} ↪ pom_rmom_sound_grouped_collision_tuple D where
  toFun f := ⟨f.1, (Finset.mem_filter.mp f.2).2⟩
  inj' := by
    intro a b h
    cases a
    cases b
    cases h
    rfl

/-- A concrete finset enumeration of the grouped synchronized collision tuples. -/
noncomputable def pom_rmom_sound_grouped_collision_tuple_finset (D : pom_rmom_sound_data) :
    Finset (pom_rmom_sound_grouped_collision_tuple D) :=
  ((Finset.univ.filter fun f : pom_rmom_sound_grouped_tuple D =>
      (∀ x, D.language (f x)) ∧ ∀ x y, f x = f y).attach).map
    (pom_rmom_sound_grouped_collision_tuple_embedding D)

/-- A concrete fintype structure on grouped synchronized collision tuples. -/
noncomputable def pom_rmom_sound_grouped_collision_tuple_fintype (D : pom_rmom_sound_data) :
    Fintype (pom_rmom_sound_grouped_collision_tuple D) where
  elems := pom_rmom_sound_grouped_collision_tuple_finset D
  complete x := by
    refine Finset.mem_map.2 ?_
    refine ⟨⟨x.1, Finset.mem_filter.2 ⟨Finset.mem_univ x.1, x.2⟩⟩, ?_, rfl⟩
    simp

/-- The embedding from the filtered flat tuple enumeration to the flat collision subtype. -/
def pom_rmom_sound_flat_collision_tuple_embedding (D : pom_rmom_sound_data) :
    {f // f ∈ Finset.univ.filter fun g : pom_rmom_sound_flat_tuple D =>
      (∀ x, D.language (g x)) ∧ ∀ x y, g x = g y} ↪ pom_rmom_sound_flat_collision_tuple D where
  toFun f := ⟨f.1, (Finset.mem_filter.mp f.2).2⟩
  inj' := by
    intro a b h
    cases a
    cases b
    cases h
    rfl

/-- A concrete finset enumeration of the flat synchronized collision tuples. -/
noncomputable def pom_rmom_sound_flat_collision_tuple_finset (D : pom_rmom_sound_data) :
    Finset (pom_rmom_sound_flat_collision_tuple D) :=
  ((Finset.univ.filter fun f : pom_rmom_sound_flat_tuple D =>
      (∀ x, D.language (f x)) ∧ ∀ x y, f x = f y).attach).map
    (pom_rmom_sound_flat_collision_tuple_embedding D)

/-- A concrete fintype structure on flat synchronized collision tuples. -/
noncomputable def pom_rmom_sound_flat_collision_tuple_fintype (D : pom_rmom_sound_data) :
    Fintype (pom_rmom_sound_flat_collision_tuple D) where
  elems := pom_rmom_sound_flat_collision_tuple_finset D
  complete x := by
    refine Finset.mem_map.2 ?_
    refine ⟨⟨x.1, Finset.mem_filter.2 ⟨Finset.mem_univ x.1, x.2⟩⟩, ?_, rfl⟩
    simp

/-- The grouped moment compiler count. -/
noncomputable def pom_rmom_sound_grouped_compiler (D : pom_rmom_sound_data) : ℕ :=
  by
    classical
    let _ := pom_rmom_sound_grouped_collision_tuple_fintype D
    exact Fintype.card (pom_rmom_sound_grouped_collision_tuple D)

/-- The flat moment compiler count. -/
noncomputable def pom_rmom_sound_flat_compiler (D : pom_rmom_sound_data) : ℕ :=
  by
    classical
    let _ := pom_rmom_sound_flat_collision_tuple_fintype D
    exact Fintype.card (pom_rmom_sound_flat_collision_tuple D)

namespace pom_rmom_sound_data

/-- Paper-facing RMOM soundness statement: the grouped `p`-then-`q` compiler and the flat
`pq`-fold compiler count the same synchronized collision language. -/
def pom_rmom_sound_statement (D : pom_rmom_sound_data) : Prop :=
  pom_rmom_sound_grouped_compiler D = pom_rmom_sound_flat_compiler D

end pom_rmom_sound_data

open pom_rmom_sound_data

/-- Paper label: `prop:pom-rmom-sound`.
The iterated `p`-then-`q` moment compiler and the one-shot `pq`-moment compiler count the same
finite synchronized language; the proof is the grouped/flat reindexing bijection on collision
tuples. -/
theorem paper_pom_rmom_sound (D : Omega.POM.pom_rmom_sound_data) : D.pom_rmom_sound_statement := by
  classical
  let _ := pom_rmom_sound_grouped_collision_tuple_fintype D
  let _ := pom_rmom_sound_flat_collision_tuple_fintype D
  simpa [pom_rmom_sound_data.pom_rmom_sound_statement, pom_rmom_sound_grouped_compiler,
    pom_rmom_sound_flat_compiler] using
    Fintype.card_congr (pom_rmom_sound_collision_tuple_equiv D)

end Omega.POM
