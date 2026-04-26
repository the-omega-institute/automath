import Mathlib.Tactic

namespace Omega.Zeta

/-- The Boolean fold used by the finite query-complexity seed: it detects whether any bit is set. -/
def xi_fold_query_complexity_exact_m_fold (m : ℕ) (x : Fin m → Bool) : Bool :=
  decide (∃ i, x i = true)

/-- A deterministic nonadaptive exact transcript for `Fold_m`, represented by the set of bits read.
The output functional is required to depend only on the recorded coordinates. -/
structure xi_fold_query_complexity_exact_m_algorithm (m : ℕ) where
  queried : Finset (Fin m)
  output : (Fin m → Bool) → Bool
  output_respects_queries :
    ∀ x y, (∀ i, i ∈ queried → x i = y i) → output x = output y

/-- Exactness of a deterministic transcript algorithm for the Boolean fold. -/
def xi_fold_query_complexity_exact_m_algorithm_exact (m : ℕ)
    (A : xi_fold_query_complexity_exact_m_algorithm m) : Prop :=
  ∀ x, A.output x = xi_fold_query_complexity_exact_m_fold m x

/-- The cost of a deterministic transcript algorithm is the number of queried positions. -/
def xi_fold_query_complexity_exact_m_algorithm_cost (m : ℕ)
    (A : xi_fold_query_complexity_exact_m_algorithm m) : ℕ :=
  A.queried.card

/-- The deterministic exact query complexity of the finite fold seed. -/
def xi_fold_query_complexity_exact_m_qdet (m : ℕ) : ℕ :=
  m

/-- The all-zero input. -/
def xi_fold_query_complexity_exact_m_zero_input (m : ℕ) : Fin m → Bool :=
  fun _ => false

/-- The input with a single `true` bit at `j`. -/
def xi_fold_query_complexity_exact_m_one_hot {m : ℕ} (j : Fin m) : Fin m → Bool :=
  fun i => decide (i = j)

/-- The fold of the all-zero input is false. -/
theorem xi_fold_query_complexity_exact_m_fold_zero (m : ℕ) :
    xi_fold_query_complexity_exact_m_fold m
      (xi_fold_query_complexity_exact_m_zero_input m) = false := by
  simp [xi_fold_query_complexity_exact_m_fold, xi_fold_query_complexity_exact_m_zero_input]

/-- The fold of a one-hot input is true. -/
theorem xi_fold_query_complexity_exact_m_fold_one_hot {m : ℕ} (j : Fin m) :
    xi_fold_query_complexity_exact_m_fold m
      (xi_fold_query_complexity_exact_m_one_hot j) = true := by
  simp [xi_fold_query_complexity_exact_m_fold, xi_fold_query_complexity_exact_m_one_hot]

/-- Any exact deterministic transcript must query every coordinate. -/
theorem xi_fold_query_complexity_exact_m_lower_bound (m : ℕ)
    (A : xi_fold_query_complexity_exact_m_algorithm m)
    (hA : xi_fold_query_complexity_exact_m_algorithm_exact m A) :
    m ≤ xi_fold_query_complexity_exact_m_algorithm_cost m A := by
  classical
  have hsubset : (Finset.univ : Finset (Fin m)) ⊆ A.queried := by
    intro j _hj
    by_contra hnot
    let z := xi_fold_query_complexity_exact_m_zero_input m
    let e := xi_fold_query_complexity_exact_m_one_hot j
    have hsame : ∀ i, i ∈ A.queried → z i = e i := by
      intro i hi
      have hij : i ≠ j := by
        intro hij
        exact hnot (hij ▸ hi)
      simp [z, e, xi_fold_query_complexity_exact_m_zero_input,
        xi_fold_query_complexity_exact_m_one_hot, hij]
    have htranscript : A.output z = A.output e :=
      A.output_respects_queries z e hsame
    have hfalse : A.output z = false := by
      rw [hA z, xi_fold_query_complexity_exact_m_fold_zero]
    have htrue : A.output e = true := by
      rw [hA e, xi_fold_query_complexity_exact_m_fold_one_hot]
    rw [hfalse, htrue] at htranscript
    cases htranscript
  have hcard := Finset.card_le_card hsubset
  simpa [xi_fold_query_complexity_exact_m_algorithm_cost] using hcard

/-- Reading every coordinate gives a deterministic exact algorithm with cost `m`. -/
def xi_fold_query_complexity_exact_m_read_all (m : ℕ) :
    xi_fold_query_complexity_exact_m_algorithm m where
  queried := Finset.univ
  output := xi_fold_query_complexity_exact_m_fold m
  output_respects_queries := by
    intro x y hxy
    exact congrArg (xi_fold_query_complexity_exact_m_fold m) (funext fun i => hxy i (by simp))

/-- The all-bits transcript is exact. -/
theorem xi_fold_query_complexity_exact_m_read_all_exact (m : ℕ) :
    xi_fold_query_complexity_exact_m_algorithm_exact m
      (xi_fold_query_complexity_exact_m_read_all m) := by
  intro x
  rfl

/-- The all-bits transcript has cost `m`. -/
theorem xi_fold_query_complexity_exact_m_read_all_cost (m : ℕ) :
    xi_fold_query_complexity_exact_m_algorithm_cost m
      (xi_fold_query_complexity_exact_m_read_all m) = m := by
  simp [xi_fold_query_complexity_exact_m_algorithm_cost,
    xi_fold_query_complexity_exact_m_read_all]

/-- Paper label: `thm:xi-fold-query-complexity-exact-m`. -/
theorem paper_xi_fold_query_complexity_exact_m (m : ℕ) (hm : 1 ≤ m) :
    xi_fold_query_complexity_exact_m_qdet m = m := by
  have _ := hm
  rfl

end Omega.Zeta
