import Mathlib
import Omega.POM.IndependenceDpRadius2

namespace Omega.POM

open Matrix

/-- The local `a_t = a_{t-1} + a_{t-2}` update matrix. -/
def pomIndUpdate2 : Matrix (Fin 3) (Fin 3) ℕ :=
  !![1, 1, 0;
    1, 0, 0;
    0, 1, 0]

/-- The local `a_t = a_{t-1} + a_{t-3}` update matrix. -/
def pomIndUpdate3 : Matrix (Fin 3) (Fin 3) ℕ :=
  !![1, 0, 1;
    1, 0, 0;
    0, 1, 0]

/-- The state vector `(a_t, a_{t-1}, a_{t-2})`. -/
def pomStateVector (a b c : ℕ) : Fin 3 → ℕ
  | 0 => a
  | 1 => b
  | 2 => c

/-- Explicit matrix action on a `3`-state vector. -/
def pomMatrixAction (A : Matrix (Fin 3) (Fin 3) ℕ) (v : Fin 3 → ℕ) : Fin 3 → ℕ :=
  fun i => ∑ j, A i j * v j

/-- Scalar version of the local update. -/
def pomTripleStep : ℕ → ℕ × ℕ × ℕ → ℕ × ℕ × ℕ
  | 2, (a, b, _) => (a + b, a, b)
  | 3, (a, b, c) => (a + c, a, b)
  | _, t => t

/-- The "single block" condition: every consecutive gap is at most `2`. -/
def pomSingleBlockRadius2 : List ℕ → Prop
  | [] => True
  | [_] => True
  | i :: j :: rest => j ≤ i + 2 ∧ pomSingleBlockRadius2 (j :: rest)

/-- Local letters extracted from ordered vertices: `3` for a dense triple, `2` otherwise. -/
def pomLocalLetters : List ℕ → List ℕ
  | i :: j :: k :: rest =>
      (if k = i + 2 then 3 else 2) :: pomLocalLetters (j :: k :: rest)
  | _ => []

/-- Scalar word evaluation starting from a chosen previous pair and seed triple. -/
def pomTripleEvalAux (prev₂ prev₁ : ℕ) : ℕ × ℕ × ℕ → List ℕ → ℕ × ℕ × ℕ
  | triple, [] => triple
  | triple, k :: rest =>
      let σ := if k = prev₂ + 2 then 3 else 2
      pomTripleEvalAux prev₁ k (pomTripleStep σ triple) rest

/-- Matrix-word evaluation starting from a chosen previous pair and seed state. -/
def pomMatrixEvalAux (prev₂ prev₁ : ℕ) : (Fin 3 → ℕ) → List ℕ → Fin 3 → ℕ
  | v, [] => v
  | v, k :: rest =>
      let A := if k = prev₂ + 2 then pomIndUpdate3 else pomIndUpdate2
      pomMatrixEvalAux prev₁ k (pomMatrixAction A v) rest

/-- Scalar evaluation attached to the ordered vertex list. -/
def pomTripleEval : List ℕ → ℕ × ℕ × ℕ
  | [] => (1, 0, 0)
  | [_] => (2, 1, 0)
  | i :: j :: rest =>
      let seed := if j ≤ i + 2 then (3, 2, 1) else (4, 2, 1)
      pomTripleEvalAux i j seed rest

/-- Matrix-word evaluation attached to the ordered vertex list. -/
def pomMatrixEval : List ℕ → Fin 3 → ℕ
  | [] => pomStateVector 1 0 0
  | [_] => pomStateVector 2 1 0
  | i :: j :: rest =>
      let seed := if j ≤ i + 2 then pomStateVector 3 2 1 else pomStateVector 4 2 1
      pomMatrixEvalAux i j seed rest

/-- The paper-facing matrix grammar proposition: on a single radius-`2` block, the fixed local
update matrices evaluate the same word as the scalar recurrence on the ordered index list. -/
def pomIndMatrixGrammar (idx : List ℕ) : Prop :=
  pomSingleBlockRadius2 idx →
    pomMatrixEval idx =
      pomStateVector (pomTripleEval idx).1 (pomTripleEval idx).2.1 (pomTripleEval idx).2.2

lemma pomIndUpdate2_action (v : Fin 3 → ℕ) :
    pomMatrixAction pomIndUpdate2 v = pomStateVector (v 0 + v 1) (v 0) (v 1) := by
  ext i
  fin_cases i <;>
    simp [pomMatrixAction, pomIndUpdate2, pomStateVector, Fin.sum_univ_three]

lemma pomIndUpdate3_action (v : Fin 3 → ℕ) :
    pomMatrixAction pomIndUpdate3 v = pomStateVector (v 0 + v 2) (v 0) (v 1) := by
  ext i
  fin_cases i <;>
    simp [pomMatrixAction, pomIndUpdate3, pomStateVector, Fin.sum_univ_three]

lemma pomMatrixEvalAux_eq_pomTripleEvalAux (prev₂ prev₁ : ℕ) :
    ∀ (triple : ℕ × ℕ × ℕ) (rest : List ℕ),
      pomMatrixEvalAux prev₂ prev₁
          (pomStateVector triple.1 triple.2.1 triple.2.2) rest =
        pomStateVector (pomTripleEvalAux prev₂ prev₁ triple rest).1
          (pomTripleEvalAux prev₂ prev₁ triple rest).2.1
          (pomTripleEvalAux prev₂ prev₁ triple rest).2.2 := by
  intro triple rest
  induction rest generalizing prev₂ prev₁ triple with
  | nil =>
      rfl
  | cons k rest ih =>
      dsimp [pomMatrixEvalAux, pomTripleEvalAux]
      by_cases hk : k = prev₂ + 2
      · simpa [hk, pomIndUpdate3_action, pomTripleStep] using
          ih prev₁ (prev₂ + 2) (triple.1 + triple.2.2, triple.1, triple.2.1)
      · simpa [hk, pomIndUpdate2_action, pomTripleStep] using
          ih prev₁ k (triple.1 + triple.2.1, triple.1, triple.2.1)

/-- Paper label: `prop:pom-ind-matrix-grammar`.
For a strictly increasing ordered index list, the single-block radius-`2` recurrence is equivalent
to a word in the two fixed update matrices `M₂` and `M₃`. -/
theorem paper_pom_ind_matrix_grammar (idx : List Nat)
    (hstrict : idx.Pairwise fun a b => a < b) : pomIndMatrixGrammar idx := by
  have _ := hstrict
  intro hblock
  cases idx with
  | nil =>
      rfl
  | cons i rest =>
      cases rest with
      | nil =>
          rfl
      | cons j rest =>
          have hij : j ≤ i + 2 := hblock.1
          simpa [pomMatrixEval, pomTripleEval, hij] using
            pomMatrixEvalAux_eq_pomTripleEvalAux i j (3, 2, 1) rest

end Omega.POM
