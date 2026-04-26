import Mathlib.Tactic
import Omega.POM.FiberSignedIndexPeriodicity

namespace Omega.POM

/-- The concrete one-point maximum-fiber family used for the stable max-fiber table. -/
abbrev pom_maxfiber_signed_index_extinction_periodic_maxfiber (_m : ℕ) := Fin 1

/-- The graph-shape component lengths for the stable maximum-fiber branch. -/
def pom_maxfiber_signed_index_extinction_periodic_component_lengths (m : ℕ) : List ℕ :=
  if Even m then
    [m / 2]
  else
    [(m - 1) / 2, 1]

/-- The componentwise signed index sequence `J_l = I_l(-1)`. -/
def pom_maxfiber_signed_index_extinction_periodic_J (l : ℕ) : ℤ :=
  pathIndSetPolyNegOne l

/-- The signed index of the stable maximum-fiber branch. -/
def pom_maxfiber_signed_index_extinction_periodic_signed_index (m : ℕ) : ℤ :=
  (pom_maxfiber_signed_index_extinction_periodic_component_lengths m).map
      pom_maxfiber_signed_index_extinction_periodic_J
    |>.prod

/-- Concrete data for the stable max-fiber signed-index table. -/
structure pom_maxfiber_signed_index_extinction_periodic_data where
  m : ℕ
  x : pom_maxfiber_signed_index_extinction_periodic_maxfiber m

private theorem pom_maxfiber_signed_index_extinction_periodic_mod6 (l : ℕ) :
    pom_maxfiber_signed_index_extinction_periodic_J l =
      pom_maxfiber_signed_index_extinction_periodic_J (l % 6) := by
  unfold pom_maxfiber_signed_index_extinction_periodic_J
  conv_lhs => rw [← Nat.mod_add_div l 6]
  induction l / 6 with
  | zero =>
      simp
  | succ k ih =>
      rw [show l % 6 + 6 * (k + 1) = (l % 6 + 6 * k) + 6 by ring]
      rw [(paper_pom_fiber_signed_index_periodicity (l % 6 + 6 * k)).1]
      exact ih

private theorem pom_maxfiber_signed_index_extinction_periodic_J_eq_one {k : ℕ}
    (hk : k % 6 = 0 ∨ k % 6 = 5) :
    pom_maxfiber_signed_index_extinction_periodic_J k = 1 := by
  rw [pom_maxfiber_signed_index_extinction_periodic_mod6 k]
  rcases hk with hk | hk <;> simp [pom_maxfiber_signed_index_extinction_periodic_J, hk]

private theorem pom_maxfiber_signed_index_extinction_periodic_J_eq_neg_one {k : ℕ}
    (hk : k % 6 = 2 ∨ k % 6 = 3) :
    pom_maxfiber_signed_index_extinction_periodic_J k = -1 := by
  rw [pom_maxfiber_signed_index_extinction_periodic_mod6 k]
  rcases hk with hk | hk <;> simp [pom_maxfiber_signed_index_extinction_periodic_J, hk,
    pathIndSetPolyNegOne]

private theorem pom_maxfiber_signed_index_extinction_periodic_J_eq_zero {k : ℕ}
    (hk : k % 6 = 1 ∨ k % 6 = 4) :
    pom_maxfiber_signed_index_extinction_periodic_J k = 0 := by
  rw [pom_maxfiber_signed_index_extinction_periodic_mod6 k]
  rcases hk with hk | hk <;> simp [pom_maxfiber_signed_index_extinction_periodic_J, hk,
    pathIndSetPolyNegOne]

/-- The concrete statement of the max-fiber extinction law and period-`6` table. -/
def pom_maxfiber_signed_index_extinction_periodic_data.statement
    (D : pom_maxfiber_signed_index_extinction_periodic_data) : Prop :=
  (Odd D.m → pom_maxfiber_signed_index_extinction_periodic_signed_index D.m = 0) ∧
    (∀ k : ℕ, D.m = 2 * k →
      pom_maxfiber_signed_index_extinction_periodic_signed_index D.m =
        pom_maxfiber_signed_index_extinction_periodic_J k) ∧
    (∀ k : ℕ, D.m = 2 * k →
      (k % 6 = 0 ∨ k % 6 = 5 →
        pom_maxfiber_signed_index_extinction_periodic_signed_index D.m = 1) ∧
      (k % 6 = 2 ∨ k % 6 = 3 →
        pom_maxfiber_signed_index_extinction_periodic_signed_index D.m = -1) ∧
      (k % 6 = 1 ∨ k % 6 = 4 →
        pom_maxfiber_signed_index_extinction_periodic_signed_index D.m = 0))

/-- Paper label: `cor:pom-maxfiber-signed-index-extinction-periodic`. -/
theorem paper_pom_maxfiber_signed_index_extinction_periodic
    (D : pom_maxfiber_signed_index_extinction_periodic_data) : D.statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro hm
    have hnot : ¬ Even D.m := by
      rintro ⟨j, hj⟩
      rcases hm with ⟨i, hi⟩
      omega
    simp [pom_maxfiber_signed_index_extinction_periodic_signed_index,
      pom_maxfiber_signed_index_extinction_periodic_component_lengths,
      pom_maxfiber_signed_index_extinction_periodic_J, hnot]
  · intro k hk
    have heven : Even D.m := by
      use k
      omega
    have hdiv : D.m / 2 = k := by omega
    simp [pom_maxfiber_signed_index_extinction_periodic_signed_index,
      pom_maxfiber_signed_index_extinction_periodic_component_lengths,
      pom_maxfiber_signed_index_extinction_periodic_J, heven, hdiv]
  · intro k hk
    have hsigned :
        pom_maxfiber_signed_index_extinction_periodic_signed_index D.m =
          pom_maxfiber_signed_index_extinction_periodic_J k := by
      have heven : Even D.m := by
        use k
        omega
      have hdiv : D.m / 2 = k := by omega
      simp [pom_maxfiber_signed_index_extinction_periodic_signed_index,
        pom_maxfiber_signed_index_extinction_periodic_component_lengths,
        pom_maxfiber_signed_index_extinction_periodic_J, heven, hdiv]
    refine ⟨?_, ?_, ?_⟩
    · intro hmod
      rw [hsigned]
      exact pom_maxfiber_signed_index_extinction_periodic_J_eq_one hmod
    · intro hmod
      rw [hsigned]
      exact pom_maxfiber_signed_index_extinction_periodic_J_eq_neg_one hmod
    · intro hmod
      rw [hsigned]
      exact pom_maxfiber_signed_index_extinction_periodic_J_eq_zero hmod

end Omega.POM
