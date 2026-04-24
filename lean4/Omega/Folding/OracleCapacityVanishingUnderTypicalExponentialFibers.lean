import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic
import Omega.Folding.OracleCapacityClosedForm

namespace Omega.Folding

open scoped BigOperators

noncomputable section

/-- Fiber size of the folding map at an output symbol. -/
def fold_oracle_capacity_vanishing_under_typical_exponential_fibers_fiber_size
    {m k : ℕ} (fold : Fin (2 ^ m) → Fin k) (x : Fin k) : ℕ :=
  Finset.card <| Finset.univ.filter fun ω : Fin (2 ^ m) => fold ω = x

private theorem fold_oracle_capacity_vanishing_under_typical_exponential_fibers_fiber_size_eq_subtype
    {m k : ℕ} (fold : Fin (2 ^ m) → Fin k) (x : Fin k) :
    fold_oracle_capacity_vanishing_under_typical_exponential_fibers_fiber_size fold x =
      Fintype.card {ω : Fin (2 ^ m) // fold ω = x} := by
  symm
  simpa [fold_oracle_capacity_vanishing_under_typical_exponential_fibers_fiber_size] using
    (Fintype.card_ofFinset
      (s := Finset.univ.filter fun ω : Fin (2 ^ m) => fold ω = x)
      (H := by
        intro ω
        constructor <;> intro h <;> simpa using h))

/-- Expectation under the uniform microstate pushforward of the fiber-size statistic. -/
def fold_oracle_capacity_vanishing_under_typical_exponential_fibers_pushforward
    {m k : ℕ} (fold : Fin (2 ^ m) → Fin k) (φ : ℕ → ℝ) : ℝ :=
  (∑ x : Fin k,
      (fold_oracle_capacity_vanishing_under_typical_exponential_fibers_fiber_size fold x : ℝ) *
        φ (fold_oracle_capacity_vanishing_under_typical_exponential_fibers_fiber_size fold x)) /
    (2 ^ m : ℝ)

/-- Normalized `B`-bit oracle success fraction. -/
def fold_oracle_capacity_vanishing_under_typical_exponential_fibers_success
    {m k : ℕ} (fold : Fin (2 ^ m) → Fin k) (B : ℕ) : ℝ :=
  (Omega.POM.bbitOracleCapacity fold B : ℝ) / (2 ^ m : ℝ)

private theorem fold_oracle_capacity_vanishing_under_typical_exponential_fibers_truncate_identity
    (d T : ℕ) :
    (Nat.min d T : ℝ) = (d : ℝ) * min (1 : ℝ) ((T : ℝ) / (d : ℝ)) := by
  by_cases hd : d = 0
  · subst hd
    simp
  · have hdpos : 0 < (d : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hd
    by_cases hle : d ≤ T
    · have hratio : (1 : ℝ) ≤ (T : ℝ) / (d : ℝ) := by
        exact (one_le_div hdpos).2 (by exact_mod_cast hle)
      simp [Nat.min_eq_left hle, min_eq_left hratio]
    · have hTd : T ≤ d := Nat.le_of_not_ge hle
      have hratio : (T : ℝ) / (d : ℝ) ≤ 1 := by
        exact (div_le_one hdpos).2 (by exact_mod_cast hTd)
      simp [Nat.min_eq_right hTd, min_eq_right hratio]
      field_simp [hd]

private theorem fold_oracle_capacity_vanishing_under_typical_exponential_fibers_fiber_mass
    {m k : ℕ} (fold : Fin (2 ^ m) → Fin k) :
    ∑ x : Fin k, fold_oracle_capacity_vanishing_under_typical_exponential_fibers_fiber_size fold x =
      2 ^ m := by
  classical
  symm
  simpa [fold_oracle_capacity_vanishing_under_typical_exponential_fibers_fiber_size] using
    (Finset.card_eq_sum_card_fiberwise
      (f := fold) (s := Finset.univ) (t := Finset.univ) (by
        intro ω hω
        simp))

private theorem fold_oracle_capacity_vanishing_under_typical_exponential_fibers_split_bound
    (d T threshold : ℕ) (hthreshold : 0 < threshold) :
    (Nat.min d T : ℝ) ≤
      (d : ℝ) * (if d < threshold then 1 else 0) + (d : ℝ) * ((T : ℝ) / (threshold : ℝ)) := by
  by_cases hbad : d < threshold
  · have hmin_le : (Nat.min d T : ℝ) ≤ d := by
      exact_mod_cast Nat.min_le_left d T
    have hnonneg : 0 ≤ (d : ℝ) * ((T : ℝ) / (threshold : ℝ)) := by
      positivity
    calc
      (Nat.min d T : ℝ) ≤ d := hmin_le
      _ ≤ (d : ℝ) + (d : ℝ) * ((T : ℝ) / (threshold : ℝ)) := by linarith
      _ = (d : ℝ) * (if d < threshold then 1 else 0) + (d : ℝ) * ((T : ℝ) / (threshold : ℝ)) := by
            simp [hbad]
  · have hthreshold_le : threshold ≤ d := Nat.le_of_not_gt hbad
    have hmin_le : (Nat.min d T : ℝ) ≤ T := by
      exact_mod_cast Nat.min_le_right d T
    have hratio : (1 : ℝ) ≤ (d : ℝ) / (threshold : ℝ) := by
      have hthreshold_pos : 0 < (threshold : ℝ) := by
        exact_mod_cast hthreshold
      exact (one_le_div hthreshold_pos).2 (by exact_mod_cast hthreshold_le)
    have hT_le : (T : ℝ) ≤ (d : ℝ) * ((T : ℝ) / (threshold : ℝ)) := by
      calc
        (T : ℝ) = (T : ℝ) * 1 := by ring
        _ ≤ (T : ℝ) * ((d : ℝ) / (threshold : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hratio (by positivity)
        _ = (d : ℝ) * ((T : ℝ) / (threshold : ℝ)) := by ring
    have hbound : (Nat.min d T : ℝ) ≤ (d : ℝ) * ((T : ℝ) / (threshold : ℝ)) := le_trans hmin_le hT_le
    simpa [hbad] using hbound

/-- Paper label: `thm:fold-oracle-capacity-vanishing-under-typical-exponential-fibers`.
The normalized oracle success ratio is the expectation of `min(1, 2^B / D_m)` under the uniform
microstate pushforward. Splitting on the event `D_m < 2^(α m)` gives the finite upper bound that
drives the vanishing argument; any target success level `η` therefore forces the residual budget
term to dominate `η` up to the exceptional mass. -/
theorem paper_fold_oracle_capacity_vanishing_under_typical_exponential_fibers
    {m k : ℕ} (fold : Fin (2 ^ m) → Fin k) (B α : ℕ) :
    fold_oracle_capacity_vanishing_under_typical_exponential_fibers_success fold B =
      fold_oracle_capacity_vanishing_under_typical_exponential_fibers_pushforward
        fold (fun d => min (1 : ℝ) (((2 ^ B : ℕ) : ℝ) / (d : ℝ))) ∧
    fold_oracle_capacity_vanishing_under_typical_exponential_fibers_success fold B ≤
      fold_oracle_capacity_vanishing_under_typical_exponential_fibers_pushforward
          fold (fun d => if d < 2 ^ (α * m) then 1 else 0) +
        (((2 ^ B : ℕ) : ℝ) / ((2 ^ (α * m) : ℕ) : ℝ)) ∧
    ∀ η : ℝ,
      η ≤ fold_oracle_capacity_vanishing_under_typical_exponential_fibers_success fold B →
      η -
          fold_oracle_capacity_vanishing_under_typical_exponential_fibers_pushforward
            fold (fun d => if d < 2 ^ (α * m) then 1 else 0) ≤
        (((2 ^ B : ℕ) : ℝ) / ((2 ^ (α * m) : ℕ) : ℝ)) := by
  let d : Fin k → ℕ :=
    fun x => fold_oracle_capacity_vanishing_under_typical_exponential_fibers_fiber_size fold x
  have hsuccess_eq :
      fold_oracle_capacity_vanishing_under_typical_exponential_fibers_success fold B =
        fold_oracle_capacity_vanishing_under_typical_exponential_fibers_pushforward
          fold (fun d => min (1 : ℝ) (((2 ^ B : ℕ) : ℝ) / (d : ℝ))) := by
    have hcap :
        (Omega.POM.bbitOracleCapacity fold B : ℝ) =
          ∑ x : Fin k, (Nat.min (d x) (2 ^ B) : ℝ) := by
      simpa [d, fold_oracle_capacity_vanishing_under_typical_exponential_fibers_fiber_size_eq_subtype]
        using
        congrArg (fun n : ℕ => (n : ℝ)) (paper_fold_oracle_capacity_closed_form fold B)
    calc
      fold_oracle_capacity_vanishing_under_typical_exponential_fibers_success fold B
          = (∑ x : Fin k, (Nat.min (d x) (2 ^ B) : ℝ)) / (2 ^ m : ℝ) := by
              simp [fold_oracle_capacity_vanishing_under_typical_exponential_fibers_success, hcap]
      _ = (∑ x : Fin k, (d x : ℝ) * min (1 : ℝ) (((2 ^ B : ℕ) : ℝ) / (d x : ℝ))) / (2 ^ m : ℝ) := by
            simp_rw [fold_oracle_capacity_vanishing_under_typical_exponential_fibers_truncate_identity]
      _ =
          fold_oracle_capacity_vanishing_under_typical_exponential_fibers_pushforward
            fold (fun d => min (1 : ℝ) (((2 ^ B : ℕ) : ℝ) / (d : ℝ))) := by
              simp [fold_oracle_capacity_vanishing_under_typical_exponential_fibers_pushforward, d]
  have hthreshold_pos : 0 < 2 ^ (α * m) := by positivity
  have hupper :
      fold_oracle_capacity_vanishing_under_typical_exponential_fibers_success fold B ≤
        fold_oracle_capacity_vanishing_under_typical_exponential_fibers_pushforward
            fold (fun d => if d < 2 ^ (α * m) then 1 else 0) +
          (((2 ^ B : ℕ) : ℝ) / ((2 ^ (α * m) : ℕ) : ℝ)) := by
    have hcap :
        fold_oracle_capacity_vanishing_under_typical_exponential_fibers_success fold B =
          (∑ x : Fin k, (Nat.min (d x) (2 ^ B) : ℝ)) / (2 ^ m : ℝ) := by
      have hcap' :
          (Omega.POM.bbitOracleCapacity fold B : ℝ) = ∑ x : Fin k, (Nat.min (d x) (2 ^ B) : ℝ) := by
        simpa [d, fold_oracle_capacity_vanishing_under_typical_exponential_fibers_fiber_size_eq_subtype]
          using
          congrArg (fun n : ℕ => (n : ℝ)) (paper_fold_oracle_capacity_closed_form fold B)
      simp [fold_oracle_capacity_vanishing_under_typical_exponential_fibers_success, hcap']
    have hsum_bound :
        (∑ x : Fin k, (Nat.min (d x) (2 ^ B) : ℝ)) ≤
          ∑ x : Fin k,
            ((d x : ℝ) * (if d x < 2 ^ (α * m) then 1 else 0) +
              (d x : ℝ) * (((2 ^ B : ℕ) : ℝ) / ((2 ^ (α * m) : ℕ) : ℝ))) := by
      refine Finset.sum_le_sum ?_
      intro x hx
      exact fold_oracle_capacity_vanishing_under_typical_exponential_fibers_split_bound
        (d x) (2 ^ B) (2 ^ (α * m)) hthreshold_pos
    have hmass :
        (∑ x : Fin k, (d x : ℝ)) / (2 ^ m : ℝ) = 1 := by
      have hmass_nat :=
        fold_oracle_capacity_vanishing_under_typical_exponential_fibers_fiber_mass fold
      have hmass_real :
          (∑ x : Fin k, (d x : ℝ)) = (2 ^ m : ℝ) := by
        simpa using congrArg (fun n : ℕ => (n : ℝ)) hmass_nat
      rw [hmass_real]
      field_simp
    have hdenom_nonneg : 0 ≤ (2 ^ m : ℝ) := by positivity
    calc
      fold_oracle_capacity_vanishing_under_typical_exponential_fibers_success fold B
          = (∑ x : Fin k, (Nat.min (d x) (2 ^ B) : ℝ)) / (2 ^ m : ℝ) := hcap
      _ ≤
          (∑ x : Fin k,
              ((d x : ℝ) * (if d x < 2 ^ (α * m) then 1 else 0) +
                (d x : ℝ) * (((2 ^ B : ℕ) : ℝ) / ((2 ^ (α * m) : ℕ) : ℝ)))) /
            (2 ^ m : ℝ) := by
              exact div_le_div_of_nonneg_right hsum_bound hdenom_nonneg
      _ =
          fold_oracle_capacity_vanishing_under_typical_exponential_fibers_pushforward
              fold (fun d => if d < 2 ^ (α * m) then 1 else 0) +
            (((2 ^ B : ℕ) : ℝ) / ((2 ^ (α * m) : ℕ) : ℝ)) := by
              rw [Finset.sum_add_distrib, add_div]
              congr 1
              calc
                (∑ x : Fin k, (d x : ℝ) * (((2 ^ B : ℕ) : ℝ) / ((2 ^ (α * m) : ℕ) : ℝ))) /
                    (2 ^ m : ℝ)
                    =
                    (((2 ^ B : ℕ) : ℝ) / ((2 ^ (α * m) : ℕ) : ℝ)) *
                      ((∑ x : Fin k, (d x : ℝ)) / (2 ^ m : ℝ)) := by
                      have hconst :
                          (∑ x : Fin k,
                            (d x : ℝ) * (((2 ^ B : ℕ) : ℝ) / ((2 ^ (α * m) : ℕ) : ℝ))) =
                            (∑ x : Fin k, (d x : ℝ)) *
                              (((2 ^ B : ℕ) : ℝ) / ((2 ^ (α * m) : ℕ) : ℝ)) := by
                                simpa using
                                  (Finset.sum_mul (s := Finset.univ)
                                    (f := fun x : Fin k => (d x : ℝ))
                                    (((2 ^ B : ℕ) : ℝ) / ((2 ^ (α * m) : ℕ) : ℝ))).symm
                      rw [hconst, div_eq_mul_inv, div_eq_mul_inv]
                      ring
                _ = (((2 ^ B : ℕ) : ℝ) / ((2 ^ (α * m) : ℕ) : ℝ)) := by
                      rw [hmass]
                      ring
  refine ⟨hsuccess_eq, hupper, ?_⟩
  intro η hη
  linarith

end

end Omega.Folding
