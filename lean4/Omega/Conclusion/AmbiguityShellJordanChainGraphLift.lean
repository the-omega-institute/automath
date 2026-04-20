import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

namespace Omega.Conclusion

open Matrix

/-- The ambiguity-shell nilpotent block used for the graph-lift package. -/
def ambiguityShellNilpotent : Matrix (Fin 1) (Fin 1) ℚ := !![(0 : ℚ)]

/-- Concrete package for lifting a Jordan chain from the essential block to the ambiguity block.
The ambiguity block is one-dimensional, so the nonzero-eigenvalue resolvent is a `1 × 1` matrix. -/
structure AmbiguityShellJordanChainGraphLiftData where
  chainLen : ℕ
  eig : ℚ
  heig : eig ≠ 0
  ess : Fin (chainLen + 1) → ℚ

namespace AmbiguityShellJordanChainGraphLiftData

/-- The ambiguity-shell resolvent `N - λ I`. -/
def shellResolvent (D : AmbiguityShellJordanChainGraphLiftData) : Matrix (Fin 1) (Fin 1) ℚ :=
  ambiguityShellNilpotent - D.eig • (1 : Matrix (Fin 1) (Fin 1) ℚ)

/-- The scalar pivot of the `1 × 1` resolvent. -/
def pivot (D : AmbiguityShellJordanChainGraphLiftData) : ℚ :=
  D.shellResolvent 0 0

lemma pivot_eq (D : AmbiguityShellJordanChainGraphLiftData) : D.pivot = -D.eig := by
  simp [pivot, shellResolvent, ambiguityShellNilpotent]

lemma pivot_ne_zero (D : AmbiguityShellJordanChainGraphLiftData) : D.pivot ≠ 0 := by
  rw [D.pivot_eq]
  exact neg_ne_zero.mpr D.heig

/-- For a `1 × 1` matrix, invertibility is equivalent to its single entry being nonzero. -/
def shellResolventInvertible (D : AmbiguityShellJordanChainGraphLiftData) : Prop :=
  D.pivot ≠ 0

lemma shellResolvent_invertible (D : AmbiguityShellJordanChainGraphLiftData) :
    D.shellResolventInvertible := by
  exact D.pivot_ne_zero

/-- Recurrence defining the ambiguity coordinates of the lifted Jordan chain. -/
def graphLiftRecurrence (D : AmbiguityShellJordanChainGraphLiftData)
    (x : Fin (D.chainLen + 1) → ℚ) : Prop :=
  D.pivot * x 0 = D.ess 0 ∧
    ∀ i : Fin D.chainLen, D.pivot * x i.succ = D.ess i.succ - x i.castSucc

/-- Extend the essential chain by zero outside the prescribed finite range. -/
def essExt (D : AmbiguityShellJordanChainGraphLiftData) (n : ℕ) : ℚ :=
  if h : n < D.chainLen + 1 then D.ess ⟨n, h⟩ else 0

/-- Recursive ambiguity coordinates obtained by solving the resolvent equation at each step. -/
def canonicalLiftSeq (D : AmbiguityShellJordanChainGraphLiftData) : ℕ → ℚ
  | 0 => D.essExt 0 / D.pivot
  | n + 1 => (D.essExt (n + 1) - D.canonicalLiftSeq n) / D.pivot

/-- Canonical lifted Jordan chain in the ambiguity coordinate. -/
def canonicalGraphLift (D : AmbiguityShellJordanChainGraphLiftData) :
    Fin (D.chainLen + 1) → ℚ :=
  fun i => D.canonicalLiftSeq i

lemma essExt_zero (D : AmbiguityShellJordanChainGraphLiftData) : D.essExt 0 = D.ess 0 := by
  simp [essExt]

lemma essExt_succ (D : AmbiguityShellJordanChainGraphLiftData) (i : Fin D.chainLen) :
    D.essExt (i.1 + 1) = D.ess i.succ := by
  have hidx : (⟨i.1 + 1, by omega⟩ : Fin (D.chainLen + 1)) = i.succ := by
    ext
    simp
  simp [essExt, hidx]

lemma canonicalGraphLift_spec (D : AmbiguityShellJordanChainGraphLiftData) :
    D.graphLiftRecurrence D.canonicalGraphLift := by
  refine ⟨?_, ?_⟩
  · have hp : D.pivot ≠ 0 := D.pivot_ne_zero
    have h0 : D.pivot * (D.essExt 0 / D.pivot) = D.essExt 0 := by
      field_simp [hp]
    simpa [graphLiftRecurrence, canonicalGraphLift, canonicalLiftSeq, D.essExt_zero] using h0
  · intro i
    have hp : D.pivot ≠ 0 := D.pivot_ne_zero
    have hs : D.essExt (i.1 + 1) = D.ess i.succ := D.essExt_succ i
    have hstep :
        D.pivot * ((D.essExt (i.1 + 1) - D.canonicalLiftSeq i) / D.pivot) =
          D.essExt (i.1 + 1) - D.canonicalLiftSeq i := by
      field_simp [hp]
    simpa [graphLiftRecurrence, canonicalGraphLift, canonicalLiftSeq, hs] using hstep

private lemma eq_of_left_mul_eq {a b c : ℚ} (hc : c ≠ 0) (h : c * a = c * b) : a = b := by
  apply (mul_right_cancel₀ hc)
  simpa [mul_comm] using h

lemma graphLiftRecurrence_unique (D : AmbiguityShellJordanChainGraphLiftData)
    {x : Fin (D.chainLen + 1) → ℚ} (hx : D.graphLiftRecurrence x) : x = D.canonicalGraphLift := by
  ext i
  have hcan := D.canonicalGraphLift_spec
  have hpoint : ∀ n, ∀ hn : n < D.chainLen + 1, x ⟨n, hn⟩ = D.canonicalGraphLift ⟨n, hn⟩ := by
    intro n
    induction n with
    | zero =>
        intro hn
        apply eq_of_left_mul_eq D.pivot_ne_zero
        exact hx.1.trans hcan.1.symm
    | succ n ih =>
        intro hn
        have hn' : n < D.chainLen := by omega
        have hprev : x (Fin.castSucc ⟨n, hn'⟩) = D.canonicalGraphLift (Fin.castSucc ⟨n, hn'⟩) := by
          simpa using ih (Nat.lt_succ_of_lt hn')
        apply eq_of_left_mul_eq D.pivot_ne_zero
        calc
          D.pivot * x (Fin.succ ⟨n, hn'⟩) = D.ess (Fin.succ ⟨n, hn'⟩) - x (Fin.castSucc ⟨n, hn'⟩) :=
            hx.2 ⟨n, hn'⟩
          _ = D.ess (Fin.succ ⟨n, hn'⟩) - D.canonicalGraphLift (Fin.castSucc ⟨n, hn'⟩) := by
            rw [hprev]
          _ = D.pivot * D.canonicalGraphLift (Fin.succ ⟨n, hn'⟩) := by
            symm
            exact hcan.2 ⟨n, hn'⟩
  exact hpoint i.1 i.2

/-- Existence and uniqueness of the ambiguity-shell graph lift together with the invertibility of
`N - λ I` in the nonzero-eigenvalue regime. -/
def existsUniqueGraphLift (D : AmbiguityShellJordanChainGraphLiftData) : Prop :=
  D.shellResolventInvertible ∧ ∃! x : Fin (D.chainLen + 1) → ℚ, D.graphLiftRecurrence x

end AmbiguityShellJordanChainGraphLiftData

open AmbiguityShellJordanChainGraphLiftData

/-- Paper label: `thm:conclusion-ambiguity-shell-nonzero-jordan-chain-graph-lift`.
For the one-dimensional ambiguity shell, the nonzero eigenvalue hypothesis makes the resolvent
invertible, so the ambiguity coordinate of a Jordan chain is determined recursively and uniquely. -/
theorem paper_conclusion_ambiguity_shell_nonzero_jordan_chain_graph_lift
    (D : AmbiguityShellJordanChainGraphLiftData) : D.existsUniqueGraphLift := by
  refine ⟨D.shellResolvent_invertible, ?_⟩
  refine ⟨D.canonicalGraphLift, D.canonicalGraphLift_spec, ?_⟩
  intro x hx
  exact D.graphLiftRecurrence_unique hx

end Omega.Conclusion
