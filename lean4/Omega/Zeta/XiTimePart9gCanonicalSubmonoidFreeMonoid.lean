import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Pairs of finite-alphabet words, one for the first `k` letters and one for the last `l` letters. -/
abbrev XiPairWords (k l : ℕ) := List (Fin k) × List (Fin l)

/-- The canonical word map `Θ` obtained by tagging the first block with `inl` and the second with `inr`. -/
def xiThetaWord {k l : ℕ} (p : XiPairWords k l) : List (Sum (Fin k) (Fin l)) :=
  p.1.map Sum.inl ++ p.2.map Sum.inr

/-- Canonical support means that a word is obtained from a left block followed by a right block. -/
def xiCanonicalSupport {k l : ℕ} (w : List (Sum (Fin k) (Fin l))) : Prop :=
  ∃ p : XiPairWords k l, xiThetaWord p = w

/-- The subtype of canonical words. -/
abbrev XiCanonicalWord (k l : ℕ) :=
  {w : List (Sum (Fin k) (Fin l)) // xiCanonicalSupport w}

/-- Extract the first `k`-block from a tagged word. -/
def xiLeftPart {k l : ℕ} (w : List (Sum (Fin k) (Fin l))) : List (Fin k) :=
  match w with
  | [] => []
  | Sum.inl i :: t => i :: xiLeftPart t
  | Sum.inr _ :: t => xiLeftPart t

/-- Extract the last `l`-block from a tagged word. -/
def xiRightPart {k l : ℕ} (w : List (Sum (Fin k) (Fin l))) : List (Fin l) :=
  match w with
  | [] => []
  | Sum.inl _ :: t => xiRightPart t
  | Sum.inr j :: t => j :: xiRightPart t

/-- The canonical embedding `Θ` into the subtype of canonical words. -/
def xiTheta {k l : ℕ} (p : XiPairWords k l) : XiCanonicalWord k l :=
  ⟨xiThetaWord p, ⟨p, rfl⟩⟩

/-- Recover the left and right blocks of a canonical word. -/
def xiSplit {k l : ℕ} (w : XiCanonicalWord k l) : XiPairWords k l :=
  (xiLeftPart w.1, xiRightPart w.1)

/-- Componentwise concatenation on pairs of words. -/
def xiPairMul {k l : ℕ} (p q : XiPairWords k l) : XiPairWords k l :=
  (p.1 ++ q.1, p.2 ++ q.2)

/-- Canonical multiplication on tagged words obtained by splitting, concatenating, and re-encoding. -/
def xiCanonicalMulWord {k l : ℕ}
    (x y : List (Sum (Fin k) (Fin l))) : List (Sum (Fin k) (Fin l)) :=
  xiThetaWord (xiLeftPart x ++ xiLeftPart y, xiRightPart x ++ xiRightPart y)

lemma xiLeftPart_map_inr {k l : ℕ} (v : List (Fin l)) :
    xiLeftPart (List.map Sum.inr v : List (Sum (Fin k) (Fin l))) = [] := by
  induction v with
  | nil =>
      rfl
  | cons j v ih =>
      simpa [xiLeftPart] using ih

lemma xiRightPart_map_inr {k l : ℕ} (v : List (Fin l)) :
    xiRightPart (List.map Sum.inr v : List (Sum (Fin k) (Fin l))) = v := by
  induction v with
  | nil =>
      rfl
  | cons j v ih =>
      simp [xiRightPart, ih]

lemma xiLeftPart_map_inl_append_map_inr {k l : ℕ} (u : List (Fin k)) (v : List (Fin l)) :
    xiLeftPart (List.map Sum.inl u ++ List.map Sum.inr v) = u := by
  induction u with
  | nil =>
      simpa using xiLeftPart_map_inr v
  | cons i u ih =>
      simp [xiLeftPart, ih]

lemma xiRightPart_map_inl_append_map_inr {k l : ℕ} (u : List (Fin k)) (v : List (Fin l)) :
    xiRightPart (List.map Sum.inl u ++ List.map Sum.inr v) = v := by
  induction u with
  | nil =>
      simpa using xiRightPart_map_inr v
  | cons i u ih =>
      simp [xiRightPart, ih]

lemma xiLeftPart_thetaWord {k l : ℕ} (p : XiPairWords k l) :
    xiLeftPart (xiThetaWord p) = p.1 := by
  rcases p with ⟨u, v⟩
  exact xiLeftPart_map_inl_append_map_inr u v

lemma xiRightPart_thetaWord {k l : ℕ} (p : XiPairWords k l) :
    xiRightPart (xiThetaWord p) = p.2 := by
  rcases p with ⟨u, v⟩
  exact xiRightPart_map_inl_append_map_inr u v

lemma xiThetaWord_split {k l : ℕ} (w : List (Sum (Fin k) (Fin l))) (hw : xiCanonicalSupport w) :
    xiThetaWord (xiLeftPart w, xiRightPart w) = w := by
  rcases hw with ⟨p, hp⟩
  rcases p with ⟨u, v⟩
  rw [← hp]
  rw [xiLeftPart_thetaWord, xiRightPart_thetaWord]

lemma xiSplit_theta {k l : ℕ} (p : XiPairWords k l) : xiSplit (xiTheta p) = p := by
  rcases p with ⟨u, v⟩
  simp [xiSplit, xiTheta, xiLeftPart_thetaWord, xiRightPart_thetaWord]

lemma xiTheta_split {k l : ℕ} (w : XiCanonicalWord k l) : xiTheta (xiSplit w) = w := by
  apply Subtype.ext
  exact xiThetaWord_split w.1 w.2

lemma xiCanonicalMulWord_mem {k l : ℕ} (x y : List (Sum (Fin k) (Fin l)))
    (hx : xiCanonicalSupport x) (hy : xiCanonicalSupport y) :
    xiCanonicalSupport (xiCanonicalMulWord x y) := by
  rcases hx with ⟨p, hp⟩
  rcases hy with ⟨q, hq⟩
  rcases p with ⟨u, v⟩
  rcases q with ⟨u', v'⟩
  refine ⟨(u ++ u', v ++ v'), ?_⟩
  subst x y
  unfold xiCanonicalMulWord
  rw [xiLeftPart_thetaWord, xiRightPart_thetaWord]
  rw [xiLeftPart_thetaWord, xiRightPart_thetaWord]

/-- The canonical-support words are closed under the induced canonical multiplication. -/
def xiCanonicalSubmonoidClosed (k l : ℕ) : Prop :=
  ∀ x y : List (Sum (Fin k) (Fin l)),
    xiCanonicalSupport x → xiCanonicalSupport y → xiCanonicalSupport (xiCanonicalMulWord x y)

/-- Canonical multiplication on the subtype of canonical words. -/
def xiCanonicalMul {k l : ℕ} (x y : XiCanonicalWord k l) : XiCanonicalWord k l :=
  ⟨xiCanonicalMulWord x.1 y.1, xiCanonicalMulWord_mem x.1 y.1 x.2 y.2⟩

/-- `Θ` is a monoid isomorphism from pairs of free words to canonical tagged words. -/
def xiThetaIsMonoidIso (k l : ℕ) : Prop :=
  Function.Bijective (@xiTheta k l) ∧
    ∀ p q : XiPairWords k l, xiTheta (xiPairMul p q) = xiCanonicalMul (xiTheta p) (xiTheta q)

/-- Paper label: `thm:xi-time-part9g-canonical-submonoid-free-monoid`.
Canonical tagged words are closed under the split-concatenate-reencode product, and the word map
`Θ(u, v) = inl(u) ++ inr(v)` is bijective and multiplicative after splitting into the first `k`
and last `l` blocks. -/
theorem paper_xi_time_part9g_canonical_submonoid_free_monoid (k l : ℕ) :
    xiCanonicalSubmonoidClosed k l ∧ xiThetaIsMonoidIso k l := by
  refine ⟨?_, ?_⟩
  · intro x y hx hy
    exact xiCanonicalMulWord_mem x y hx hy
  · refine ⟨?_, ?_⟩
    · constructor
      · intro p q hpq
        have hsplit := congrArg xiSplit hpq
        simpa [xiSplit_theta] using hsplit
      · intro w
        exact ⟨xiSplit w, xiTheta_split w⟩
    · intro p q
      rcases p with ⟨u, v⟩
      rcases q with ⟨u', v'⟩
      apply Subtype.ext
      change xiThetaWord (xiPairMul (u, v) (u', v')) =
        xiThetaWord
          (xiLeftPart (xiThetaWord (u, v)) ++ xiLeftPart (xiThetaWord (u', v')),
            xiRightPart (xiThetaWord (u, v)) ++ xiRightPart (xiThetaWord (u', v')))
      rw [xiLeftPart_thetaWord, xiRightPart_thetaWord]
      rw [xiLeftPart_thetaWord, xiRightPart_thetaWord]
      rfl

end Omega.Zeta
