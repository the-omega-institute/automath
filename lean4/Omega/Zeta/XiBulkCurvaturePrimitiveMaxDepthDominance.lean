import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- Total depth moment `p_n = ∑_j y_j^n`. -/
def xi_bulk_curvature_primitive_max_depth_dominance_power_sum {κ : ℕ}
    (y : Fin κ → ℝ) (n : ℕ) : ℝ :=
  ∑ j : Fin κ, y j ^ n

/-- Top-depth multiplicity for a chosen maximal depth `Λ`. -/
def xi_bulk_curvature_primitive_max_depth_dominance_top_multiplicity {κ : ℕ}
    (y : Fin κ → ℝ) (Λ : ℝ) : ℝ :=
  ((Finset.univ.filter fun j : Fin κ => y j = Λ).card : ℝ)

/-- Contribution of depths strictly below the chosen top depth. -/
def xi_bulk_curvature_primitive_max_depth_dominance_submaximal_power {κ : ℕ}
    (y : Fin κ → ℝ) (Λ : ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin κ => y j ≠ Λ), y j ^ n

/-- Möbius primitive numerator `n π_n^prim`, before division by `n`. -/
def xi_bulk_curvature_primitive_max_depth_dominance_primitive_numerator {κ : ℕ}
    (y : Fin κ → ℝ) (n : ℕ) : ℝ :=
  ∑ d ∈ Nat.divisors n,
    (ArithmeticFunction.moebius d : ℝ) *
      xi_bulk_curvature_primitive_max_depth_dominance_power_sum y (n / d)

/-- The contribution of nontrivial divisors `d ≠ 1` in the primitive Möbius numerator. -/
def xi_bulk_curvature_primitive_max_depth_dominance_nontrivial_divisor_part {κ : ℕ}
    (y : Fin κ → ℝ) (n : ℕ) : ℝ :=
  ∑ d ∈ (Nat.divisors n).filter (fun d => d ≠ 1),
    (ArithmeticFunction.moebius d : ℝ) *
      xi_bulk_curvature_primitive_max_depth_dominance_power_sum y (n / d)

private lemma xi_bulk_curvature_primitive_max_depth_dominance_power_sum_split {κ : ℕ}
    (y : Fin κ → ℝ) (Λ : ℝ) (n : ℕ) :
    xi_bulk_curvature_primitive_max_depth_dominance_power_sum y n =
      xi_bulk_curvature_primitive_max_depth_dominance_top_multiplicity y Λ * Λ ^ n +
        xi_bulk_curvature_primitive_max_depth_dominance_submaximal_power y Λ n := by
  let s : Finset (Fin κ) := Finset.univ
  let f : Fin κ → ℝ := fun j => y j ^ n
  let p : Fin κ → Prop := fun j => y j = Λ
  have hsplit :
      ∑ j ∈ s, f j = ∑ j ∈ s.filter p, f j + ∑ j ∈ s.filter (fun j => ¬p j), f j := by
    simpa [s, f, p, add_comm] using
      (Finset.sum_filter_add_sum_filter_not (s := s) (p := p) (f := f)).symm
  have htop : ∑ j ∈ s.filter p, f j =
      xi_bulk_curvature_primitive_max_depth_dominance_top_multiplicity y Λ * Λ ^ n := by
    have hconst : ∑ j ∈ s.filter p, f j = ∑ _j ∈ s.filter p, Λ ^ n := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      simp [s, p] at hj
      simp [f, hj]
    calc
      ∑ j ∈ s.filter p, f j = ∑ _j ∈ s.filter p, Λ ^ n := hconst
      _ = ((s.filter p).card : ℝ) * Λ ^ n := by simp
      _ = xi_bulk_curvature_primitive_max_depth_dominance_top_multiplicity y Λ * Λ ^ n := by
            simp [xi_bulk_curvature_primitive_max_depth_dominance_top_multiplicity, s, p]
  calc
    xi_bulk_curvature_primitive_max_depth_dominance_power_sum y n = ∑ j ∈ s, f j := by
      simp [xi_bulk_curvature_primitive_max_depth_dominance_power_sum, s, f]
    _ = ∑ j ∈ s.filter p, f j + ∑ j ∈ s.filter (fun j => ¬p j), f j := hsplit
    _ = xi_bulk_curvature_primitive_max_depth_dominance_top_multiplicity y Λ * Λ ^ n +
        xi_bulk_curvature_primitive_max_depth_dominance_submaximal_power y Λ n := by
          rw [htop]
          simp [xi_bulk_curvature_primitive_max_depth_dominance_submaximal_power, s, f, p]

private lemma xi_bulk_curvature_primitive_max_depth_dominance_divisor_split {κ : ℕ}
    (y : Fin κ → ℝ) {n : ℕ} (hn : n ≠ 0) :
    xi_bulk_curvature_primitive_max_depth_dominance_primitive_numerator y n =
      xi_bulk_curvature_primitive_max_depth_dominance_power_sum y n +
        xi_bulk_curvature_primitive_max_depth_dominance_nontrivial_divisor_part y n := by
  let f : ℕ → ℝ := fun d =>
    (ArithmeticFunction.moebius d : ℝ) *
      xi_bulk_curvature_primitive_max_depth_dominance_power_sum y (n / d)
  have hfilter :
      (Nat.divisors n).filter (fun d => d = 1) = ({1} : Finset ℕ) := by
    ext d
    by_cases hd : d = 1
    · subst d
      simp [Nat.mem_divisors, hn]
    · simp [hd]
  have hsplit :
      ∑ d ∈ Nat.divisors n, f d =
        ∑ d ∈ (Nat.divisors n).filter (fun d => d = 1), f d +
          ∑ d ∈ (Nat.divisors n).filter (fun d => d ≠ 1), f d := by
    simpa [add_comm] using
      (Finset.sum_filter_add_sum_filter_not
        (s := Nat.divisors n) (p := fun d => d = 1) (f := f)).symm
  calc
    xi_bulk_curvature_primitive_max_depth_dominance_primitive_numerator y n =
        ∑ d ∈ Nat.divisors n, f d := by
          simp [xi_bulk_curvature_primitive_max_depth_dominance_primitive_numerator, f]
    _ = ∑ d ∈ (Nat.divisors n).filter (fun d => d = 1), f d +
        ∑ d ∈ (Nat.divisors n).filter (fun d => d ≠ 1), f d := hsplit
    _ = xi_bulk_curvature_primitive_max_depth_dominance_power_sum y n +
        xi_bulk_curvature_primitive_max_depth_dominance_nontrivial_divisor_part y n := by
          simp [hfilter, xi_bulk_curvature_primitive_max_depth_dominance_nontrivial_divisor_part,
            f]

/-- Paper label: `prop:xi-bulk-curvature-primitive-max-depth-dominance`. The primitive Möbius
ledger splits exactly into the dominant top-depth `d = 1` contribution, the submaximal
same-period contribution, and the nontrivial-divisor remainder. -/
theorem paper_xi_bulk_curvature_primitive_max_depth_dominance {κ : ℕ}
    (y : Fin κ → ℝ) (Λ : ℝ) {n : ℕ} (hn : n ≠ 0) :
    xi_bulk_curvature_primitive_max_depth_dominance_primitive_numerator y n =
      xi_bulk_curvature_primitive_max_depth_dominance_top_multiplicity y Λ * Λ ^ n +
        xi_bulk_curvature_primitive_max_depth_dominance_submaximal_power y Λ n +
          xi_bulk_curvature_primitive_max_depth_dominance_nontrivial_divisor_part y n := by
  rw [xi_bulk_curvature_primitive_max_depth_dominance_divisor_split y hn,
    xi_bulk_curvature_primitive_max_depth_dominance_power_sum_split y Λ n]

end

end Omega.Zeta
