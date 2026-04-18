import Mathlib.Tactic

namespace Omega.POM

/-- Value-layer tokens: concrete values together with the distinguished `PROJ_NORM` token. -/
inductive ValProjectionToken where
  | atom : ℕ → ValProjectionToken
  | projNorm
deriving DecidableEq, Repr

open ValProjectionToken

/-- Value-layer words. -/
abbrev ValProjectionWord := List ValProjectionToken

/-- The atom-only word associated to a list of concrete values. -/
def atomsWord (xs : List ℕ) : ValProjectionWord :=
  xs.map atom

/-- Extract the concrete values from a word, discarding all `PROJ_NORM` tokens. -/
def atoms : ValProjectionWord → List ℕ
  | [] => []
  | atom n :: w => n :: atoms w
  | projNorm :: w => atoms w

/-- Whether the word contains at least one `PROJ_NORM` token. -/
def hasNormProj : ValProjectionWord → Bool
  | [] => false
  | atom _ :: w => hasNormProj w
  | projNorm :: _ => true

/-- Normalization pushes every `PROJ_NORM` token to the end and compresses them to at most one
terminal occurrence. -/
def normalize (w : ValProjectionWord) : ValProjectionWord :=
  atomsWord (atoms w) ++ if hasNormProj w then [projNorm] else []

/-- Count the number of `PROJ_NORM` tokens. -/
def normProjCount : ValProjectionWord → ℕ
  | [] => 0
  | atom _ :: w => normProjCount w
  | projNorm :: w => normProjCount w + 1

/-- Normal forms are exactly atom words with an optional terminal `PROJ_NORM`. -/
def IsNormalForm (w : ValProjectionWord) : Prop :=
  ∃ xs : List ℕ, ∃ b : Bool, w = atomsWord xs ++ if b then [projNorm] else []

/-- One-step rewrite rule `RZ`: merge two adjacent `PROJ_NORM` tokens. -/
inductive RewriteStep : ValProjectionWord → ValProjectionWord → Prop where
  | RZ (u v : ValProjectionWord) :
      RewriteStep (u ++ projNorm :: projNorm :: v) (u ++ projNorm :: v)
  | RNF (u v : ValProjectionWord) (n : ℕ) :
      RewriteStep (u ++ projNorm :: atom n :: v) (u ++ atom n :: projNorm :: v)

/-- Reflexive transitive closure of the rewrite system. -/
inductive RewritesToStar : ValProjectionWord → ValProjectionWord → Prop where
  | refl (w : ValProjectionWord) : RewritesToStar w w
  | tail {u v w : ValProjectionWord} :
      RewriteStep u v → RewritesToStar v w → RewritesToStar u w

lemma RewritesToStar.trans {u v w : ValProjectionWord} :
    RewritesToStar u v → RewritesToStar v w → RewritesToStar u w := by
  intro huv hvw
  induction huv with
  | refl _ =>
      exact hvw
  | tail hstep hstar ih =>
      exact RewritesToStar.tail hstep (ih hvw)

lemma RewriteStep.cons_atom {u v : ValProjectionWord} (a : ℕ) :
    RewriteStep u v → RewriteStep (atom a :: u) (atom a :: v) := by
  intro h
  cases h with
  | RZ u v =>
      simpa [List.cons_append, List.append_assoc] using RewriteStep.RZ (atom a :: u) v
  | RNF u v n =>
      simpa [List.cons_append, List.append_assoc] using RewriteStep.RNF (atom a :: u) v n

lemma RewriteStep.cons_projNorm {u v : ValProjectionWord} :
    RewriteStep u v → RewriteStep (projNorm :: u) (projNorm :: v) := by
  intro h
  cases h with
  | RZ u v =>
      simpa [List.cons_append, List.append_assoc] using RewriteStep.RZ (projNorm :: u) v
  | RNF u v n =>
      simpa [List.cons_append, List.append_assoc] using RewriteStep.RNF (projNorm :: u) v n

lemma RewritesToStar.cons_atom {u v : ValProjectionWord} (a : ℕ) :
    RewritesToStar u v → RewritesToStar (atom a :: u) (atom a :: v) := by
  intro h
  induction h with
  | refl w =>
      exact RewritesToStar.refl (atom a :: w)
  | tail hstep hstar ih =>
      exact RewritesToStar.tail (RewriteStep.cons_atom a hstep) ih

lemma RewritesToStar.cons_projNorm {u v : ValProjectionWord} :
    RewritesToStar u v → RewritesToStar (projNorm :: u) (projNorm :: v) := by
  intro h
  induction h with
  | refl w =>
      exact RewritesToStar.refl (projNorm :: w)
  | tail hstep hstar ih =>
      exact RewritesToStar.tail (RewriteStep.cons_projNorm hstep) ih

@[simp] lemma atomsWord_nil : atomsWord [] = [] := rfl

@[simp] lemma atomsWord_cons (a : ℕ) (xs : List ℕ) :
    atomsWord (a :: xs) = atom a :: atomsWord xs := rfl

@[simp] lemma normProjCount_atomsWord (xs : List ℕ) :
    normProjCount (atomsWord xs) = 0 := by
  induction xs with
  | nil =>
      rfl
  | cons _ xs ih =>
      simpa [atomsWord] using ih

@[simp] lemma normProjCount_append (u v : ValProjectionWord) :
    normProjCount (u ++ v) = normProjCount u + normProjCount v := by
  induction u with
  | nil =>
      simp [normProjCount]
  | cons t u ih =>
      cases t <;> simp [normProjCount, ih, Nat.add_comm, Nat.add_left_comm]

lemma pushProjToEnd (xs : List ℕ) :
    RewritesToStar (projNorm :: atomsWord xs) (atomsWord xs ++ [projNorm]) := by
  induction xs with
  | nil =>
      exact RewritesToStar.refl [projNorm]
  | cons a xs ih =>
      refine RewritesToStar.tail (v := atom a :: projNorm :: atomsWord xs) ?_ ?_
      · simpa [atomsWord] using RewriteStep.RNF [] (atomsWord xs) a
      · simpa [atomsWord] using RewritesToStar.cons_atom a ih

lemma pushProjToEndAndCollapse (xs : List ℕ) :
    RewritesToStar (projNorm :: (atomsWord xs ++ [projNorm])) (atomsWord xs ++ [projNorm]) := by
  induction xs with
  | nil =>
      refine RewritesToStar.tail ?_ (RewritesToStar.refl [projNorm])
      simpa using RewriteStep.RZ [] []
  | cons a xs ih =>
      refine RewritesToStar.tail (v := atom a :: projNorm :: (atomsWord xs ++ [projNorm])) ?_ ?_
      · simpa [atomsWord, List.append_assoc] using RewriteStep.RNF [] (atomsWord xs ++ [projNorm]) a
      · simpa [atomsWord, List.append_assoc] using RewritesToStar.cons_atom a ih

lemma rewritesToNormalize (w : ValProjectionWord) :
    RewritesToStar w (normalize w) := by
  induction w with
  | nil =>
      exact RewritesToStar.refl []
  | cons t w ih =>
      cases t with
      | atom a =>
          simpa [normalize, atomsWord] using RewritesToStar.cons_atom a ih
      | projNorm =>
          cases h : hasNormProj w with
          | false =>
              have h₁ : RewritesToStar (projNorm :: w) (projNorm :: normalize w) :=
                RewritesToStar.cons_projNorm ih
              have h₂ :
                  RewritesToStar (projNorm :: normalize w) (normalize (projNorm :: w)) := by
                simpa [normalize, h, atomsWord, List.append_assoc] using pushProjToEnd (atoms w)
              exact RewritesToStar.trans h₁ h₂
          | true =>
              have h₁ : RewritesToStar (projNorm :: w) (projNorm :: normalize w) :=
                RewritesToStar.cons_projNorm ih
              have h₂ :
                  RewritesToStar (projNorm :: normalize w) (normalize (projNorm :: w)) := by
                simpa [normalize, h, atomsWord, List.append_assoc] using
                  pushProjToEndAndCollapse (atoms w)
              exact RewritesToStar.trans h₁ h₂

lemma normalize_isNormalForm (w : ValProjectionWord) : IsNormalForm (normalize w) := by
  exact ⟨atoms w, hasNormProj w, rfl⟩

lemma normProjCount_normalize_le_one (w : ValProjectionWord) :
    normProjCount (normalize w) ≤ 1 := by
  cases h : hasNormProj w <;> simp [normalize, h, normProjCount]

/-- Termination of the value-layer rewriting system: every word rewrites to a normal form in which
all `PROJ_NORM` tokens have been pushed to the end and compressed to at most one occurrence.
    prop:pom-rewriting-terminating -/
theorem paper_pom_rewriting_terminating (w : ValProjectionWord) :
    ∃ w' : ValProjectionWord, IsNormalForm w' ∧ RewritesToStar w w' ∧ normProjCount w' ≤ 1 := by
  refine ⟨normalize w, normalize_isNormalForm w, rewritesToNormalize w,
    normProjCount_normalize_le_one w⟩

end Omega.POM
