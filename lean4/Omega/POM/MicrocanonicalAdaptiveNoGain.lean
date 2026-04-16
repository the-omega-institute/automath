import Mathlib.Tactic
import Omega.POM.KCollisionRootFilter

namespace Omega.POM

open scoped BigOperators

section

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The falling-factorial numerator attached to a count vector. -/
def microcanonicalCountWeight (d : α → ℕ) (c : α → ℕ) : ℚ :=
  ∏ x ∈ (Finset.univ : Finset α), (Nat.descFactorial (d x) (c x) : ℚ)

/-- The microcanonical trajectory law determined by a total budget `N`, a step count `k`,
    and the count vector `c`. -/
def microcanonicalTrajectoryProb (N k : ℕ) (d : α → ℕ) (c : α → ℕ) : ℚ :=
  microcanonicalCountWeight d c / (Nat.descFactorial N k : ℚ)

/-- Increment the count vector at the observed type `x`. -/
def incrementCount (c : α → ℕ) (x : α) : α → ℕ :=
  Function.update c x (c x + 1)

lemma microcanonicalCountWeight_increment (d c : α → ℕ) (x : α) :
    microcanonicalCountWeight d (incrementCount c x) =
      (((d x - c x : ℕ) : ℚ)) * microcanonicalCountWeight d c := by
  classical
  unfold microcanonicalCountWeight incrementCount
  have hx : x ∈ (Finset.univ : Finset α) := Finset.mem_univ x
  have hprod :
      ∏ y ∈ Finset.univ \ {x}, (Nat.descFactorial (d y) (Function.update c x (c x + 1) y) : ℚ) =
        ∏ y ∈ Finset.univ \ {x}, (Nat.descFactorial (d y) (c y) : ℚ) := by
    apply Finset.prod_congr rfl
    intro y hy
    by_cases h : y = x
    · subst h
      exfalso
      exact (Finset.mem_sdiff.mp hy).2 (by simp)
    · simp [Function.update, h]
  rw [Finset.prod_eq_mul_prod_diff_singleton hx, Finset.prod_eq_mul_prod_diff_singleton hx]
  rw [hprod]
  simp [Nat.descFactorial_succ, mul_assoc]

lemma microcanonicalTrajectoryProb_step (N k : ℕ) (d c : α → ℕ) (x : α) (hk : k < N) :
    microcanonicalTrajectoryProb N (k + 1) d (incrementCount c x) =
      microcanonicalTrajectoryProb N k d c *
        ((((d x - c x : ℕ) : ℚ)) / (((N - k : ℕ) : ℚ))) := by
  have hweight := microcanonicalCountWeight_increment d c x
  have hNk : ((N - k : ℕ) : ℚ) ≠ 0 := by
    have hNkNat : N - k ≠ 0 := by omega
    exact_mod_cast hNkNat
  have hdesc : (Nat.descFactorial N k : ℚ) ≠ 0 := by
    have hdescNat : Nat.descFactorial N k ≠ 0 := by
      intro hz
      exact (not_lt_of_ge (le_of_lt hk)) ((Nat.descFactorial_eq_zero_iff_lt).mp hz)
    exact_mod_cast hdescNat
  unfold microcanonicalTrajectoryProb
  rw [hweight, Nat.descFactorial_succ, Nat.cast_mul]
  field_simp [hNk, hdesc]

set_option maxHeartbeats 400000 in
/-- Paper-facing microcanonical no-gain statement: the falling-factorial trajectory law depends
    only on the count vector, and the next-step update is the without-replacement ratio.
    thm:pom-microcanonical-adaptive-no-gain-without-replacement -/
theorem paper_pom_microcanonical_adaptive_no_gain_without_replacement
    (N k : ℕ) (d c : α → ℕ) (x : α) (hk : k < N) :
    (∀ c' : α → ℕ, (∀ y, c y = c' y) →
      microcanonicalTrajectoryProb N k d c = microcanonicalTrajectoryProb N k d c') ∧
      microcanonicalTrajectoryProb N (k + 1) d (incrementCount c x) =
        microcanonicalTrajectoryProb N k d c *
          ((((d x - c x : ℕ) : ℚ)) / (((N - k : ℕ) : ℚ))) := by
  refine ⟨?_, microcanonicalTrajectoryProb_step N k d c x hk⟩
  intro c' hc
  simp [microcanonicalTrajectoryProb, microcanonicalCountWeight, hc]

end

end Omega.POM
