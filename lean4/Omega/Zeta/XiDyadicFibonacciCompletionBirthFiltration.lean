import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete finite-coordinate model for the dyadic Fibonacci birth filtration. Each coordinate has
a first-birth index, every coordinate is born by `topBirth`, there is an explicit witness at birth
level `3`, and every level `k ≥ 4` up to `topBirth` carries a witness as well. -/
structure xi_dyadic_fibonacci_completion_birth_filtration_data where
  coordinateCount : ℕ
  topBirth : ℕ
  firstBirth : Fin coordinateCount → ℕ
  firstBirth_le_top : ∀ i, firstBirth i ≤ topBirth
  birth_three_witness : ∃ i, firstBirth i = 3
  birth_ge_four_witness : ∀ k, 4 ≤ k → k ≤ topBirth → ∃ i, firstBirth i = k

namespace xi_dyadic_fibonacci_completion_birth_filtration_data

/-- Coordinates whose first visible appearance is exactly at level `k`. -/
def newborn_coordinates (D : xi_dyadic_fibonacci_completion_birth_filtration_data)
    (k : ℕ) : Finset (Fin D.coordinateCount) :=
  Finset.univ.filter fun i => D.firstBirth i = k

/-- Coordinates present by filtration level `n`. -/
def level_coordinates (D : xi_dyadic_fibonacci_completion_birth_filtration_data)
    (n : ℕ) : Finset (Fin D.coordinateCount) :=
  Finset.univ.filter fun i => D.firstBirth i ≤ n

/-- The transition from level `n + 1` to level `n` forgets precisely the coordinates born at
level `n + 1`. -/
def transition_coordinates (D : xi_dyadic_fibonacci_completion_birth_filtration_data)
    (n : ℕ) : Finset (Fin D.coordinateCount) :=
  (D.level_coordinates (n + 1)).filter fun i => D.firstBirth i ≤ n

end xi_dyadic_fibonacci_completion_birth_filtration_data

open xi_dyadic_fibonacci_completion_birth_filtration_data

/-- Each level is the union of its birth-index strata up to that level. -/
def xi_dyadic_fibonacci_completion_birth_filtration_level_decomposition
    (D : xi_dyadic_fibonacci_completion_birth_filtration_data) : Prop :=
  ∀ n : ℕ, ∀ i : Fin D.coordinateCount,
    i ∈ D.level_coordinates n ↔
      ∃ k ∈ Finset.range (n + 1), i ∈ D.newborn_coordinates k

/-- At the terminal birth index every coordinate has appeared, so the finite model equals its
stable completion. -/
def xi_dyadic_fibonacci_completion_birth_filtration_limit_decomposition
    (D : xi_dyadic_fibonacci_completion_birth_filtration_data) : Prop :=
  ∀ i : Fin D.coordinateCount, i ∈ D.level_coordinates D.topBirth

/-- Transition maps are coordinate deletions: passing from level `n + 1` to level `n` keeps
exactly the coordinates already born by level `n`. -/
def xi_dyadic_fibonacci_completion_birth_filtration_transition_deletes_newborn_coordinates
    (D : xi_dyadic_fibonacci_completion_birth_filtration_data) : Prop :=
  ∀ n : ℕ, ∀ i : Fin D.coordinateCount,
    i ∈ D.transition_coordinates n ↔ i ∈ D.level_coordinates n

/-- Every level from the first birth level `3` through the terminal birth level is nonempty. -/
def xi_dyadic_fibonacci_completion_birth_filtration_nonempty_each_level
    (D : xi_dyadic_fibonacci_completion_birth_filtration_data) : Prop :=
  ∀ n : ℕ, 3 ≤ n → n ≤ D.topBirth → (D.level_coordinates n).Nonempty

/-- Paper label: `thm:xi-dyadic-fibonacci-completion-birth-filtration`. In the concrete finite
birth-ledger model, each level is obtained by regrouping coordinates according to first-birth
index, the terminal level contains all coordinates, the transition maps delete exactly the newborn
coordinates, and the explicit birth witnesses make every level `n ≥ 3` nonempty. -/
theorem paper_xi_dyadic_fibonacci_completion_birth_filtration
    (D : xi_dyadic_fibonacci_completion_birth_filtration_data) :
    xi_dyadic_fibonacci_completion_birth_filtration_level_decomposition D ∧
      xi_dyadic_fibonacci_completion_birth_filtration_limit_decomposition D ∧
      xi_dyadic_fibonacci_completion_birth_filtration_transition_deletes_newborn_coordinates D ∧
      xi_dyadic_fibonacci_completion_birth_filtration_nonempty_each_level D := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n i
    constructor
    · intro hi
      have hbirth : D.firstBirth i ≤ n := by
        simpa [xi_dyadic_fibonacci_completion_birth_filtration_data.level_coordinates] using hi
      refine ⟨D.firstBirth i, ?_, ?_⟩
      · exact Finset.mem_range.2 (Nat.lt_succ_of_le hbirth)
      · simp [xi_dyadic_fibonacci_completion_birth_filtration_data.newborn_coordinates]
    · intro hi
      rcases hi with ⟨k, hk, hki⟩
      have hk_le : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.1 hk)
      have hbirth_eq : D.firstBirth i = k := by
        simpa [xi_dyadic_fibonacci_completion_birth_filtration_data.newborn_coordinates] using hki
      simp [xi_dyadic_fibonacci_completion_birth_filtration_data.level_coordinates, hbirth_eq, hk_le]
  · intro i
    simp [xi_dyadic_fibonacci_completion_birth_filtration_data.level_coordinates,
      D.firstBirth_le_top i]
  · intro n i
    constructor
    · intro hi
      have hpair : D.firstBirth i ≤ n + 1 ∧ D.firstBirth i ≤ n := by
        simpa [xi_dyadic_fibonacci_completion_birth_filtration_data.transition_coordinates,
          xi_dyadic_fibonacci_completion_birth_filtration_data.level_coordinates] using hi
      simp [xi_dyadic_fibonacci_completion_birth_filtration_data.level_coordinates, hpair.2]
    · intro hi
      have hbirth : D.firstBirth i ≤ n := by
        simpa [xi_dyadic_fibonacci_completion_birth_filtration_data.level_coordinates] using hi
      have hsucc : D.firstBirth i ≤ n + 1 := Nat.le_trans hbirth (Nat.le_succ n)
      simp [xi_dyadic_fibonacci_completion_birth_filtration_data.transition_coordinates,
        xi_dyadic_fibonacci_completion_birth_filtration_data.level_coordinates, hbirth, hsucc]
  · intro n hn htop
    rcases lt_or_eq_of_le hn with hlt | rfl
    · have hfour : 4 ≤ n := by omega
      rcases D.birth_ge_four_witness n hfour htop with ⟨i, hi⟩
      refine ⟨i, ?_⟩
      simp [xi_dyadic_fibonacci_completion_birth_filtration_data.level_coordinates, hi]
    · rcases D.birth_three_witness with ⟨i, hi⟩
      refine ⟨i, ?_⟩
      simp [xi_dyadic_fibonacci_completion_birth_filtration_data.level_coordinates, hi]

end Omega.Zeta
