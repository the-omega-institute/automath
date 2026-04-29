import Mathlib.Tactic
import Omega.Folding.FoldbinGroupoidAut0Pi1TorsionExponent

namespace Omega.Folding

/-- Concrete data for the cyclic-injection criterion on the audited foldbin `Aut₀` fundamental
group. -/
structure foldbin_groupoid_aut0_cyclic_injection_criterion_data where
  cyclicOrders : List ℕ
  exponentValue : ℕ
  cyclicOrders_eq : cyclicOrders = foldbin_groupoid_aut0_pi1_torsion_exponent_cyclic_orders
  exponentValue_eq : exponentValue = foldbin_groupoid_aut0_pi1_torsion_exponent_value

local notation "FoldbinGroupoidAut0CyclicInjectionCriterionData" =>
  foldbin_groupoid_aut0_cyclic_injection_criterion_data

/-- In the finite abelian proxy, a cyclic injection of order `n` is witnessed by a cyclic factor
whose order is a multiple of `n`. -/
def foldbin_groupoid_aut0_cyclic_injection_criterion_data.hasElementOfOrder
    (D : foldbin_groupoid_aut0_cyclic_injection_criterion_data) (n : ℕ) : Prop :=
  ∃ m ∈ D.cyclicOrders, n ∣ m

/-- Any such cyclic injection forces `n` to divide the group exponent. -/
def foldbin_groupoid_aut0_cyclic_injection_criterion_data.cyclicInjectionCriterion
    (D : foldbin_groupoid_aut0_cyclic_injection_criterion_data) (n : ℕ) : Prop :=
  D.hasElementOfOrder n → n ∣ D.exponentValue

lemma foldbin_groupoid_aut0_cyclic_injection_criterion_dvd_foldl_lcm_of_dvd_or_mem
    {l : List ℕ} {a seed : ℕ} (h : a ∣ seed ∨ a ∈ l) : a ∣ l.foldl Nat.lcm seed := by
  induction l generalizing seed with
  | nil =>
      rcases h with hseed | hmem
      · simpa using hseed
      · simp at hmem
  | cons b l ih =>
      rcases h with hseed | hmem
      · change a ∣ l.foldl Nat.lcm (Nat.lcm seed b)
        apply ih
        exact Or.inl (dvd_trans hseed (Nat.dvd_lcm_left seed b))
      · simp at hmem
        rcases hmem with hEq | hmem
        · cases hEq
          change a ∣ l.foldl Nat.lcm (Nat.lcm seed a)
          apply ih
          exact Or.inl (Nat.dvd_lcm_right seed a)
        · change a ∣ l.foldl Nat.lcm (Nat.lcm seed b)
          apply ih
          exact Or.inr hmem

lemma foldbin_groupoid_aut0_cyclic_injection_criterion_dvd_foldl_lcm_of_mem
    {l : List ℕ} {a : ℕ} (ha : a ∈ l) : a ∣ l.foldl Nat.lcm 1 := by
  exact
    foldbin_groupoid_aut0_cyclic_injection_criterion_dvd_foldl_lcm_of_dvd_or_mem
      (seed := 1) (Or.inr ha)

/-- Paper label: `cor:foldbin-groupoid-aut0-cyclic-injection-criterion`. -/
theorem paper_foldbin_groupoid_aut0_cyclic_injection_criterion
    (D : FoldbinGroupoidAut0CyclicInjectionCriterionData) (n : ℕ) :
    D.cyclicInjectionCriterion n := by
  intro hInject
  rcases hInject with ⟨m, hm, hnm⟩
  rw [D.exponentValue_eq]
  rw [D.cyclicOrders_eq] at hm
  have hmexp : m ∣ foldbin_groupoid_aut0_pi1_torsion_exponent_value := by
    simpa [foldbin_groupoid_aut0_pi1_torsion_exponent_value] using
      foldbin_groupoid_aut0_cyclic_injection_criterion_dvd_foldl_lcm_of_mem hm
  exact dvd_trans hnm hmexp

end Omega.Folding
