import Mathlib.Tactic

namespace Omega.POM

open BigOperators

private lemma pom_fiber_posterior_hamming_diversity_bool_disagree (b c : Bool) :
    (if b = c then (0 : ℝ) else 1) =
      (if b then (1 : ℝ) else 0) + (if c then (1 : ℝ) else 0) -
        2 * (if b then (1 : ℝ) else 0) * (if c then (1 : ℝ) else 0) := by
  cases b <;> cases c <;> norm_num

private lemma pom_fiber_posterior_hamming_diversity_coordinate
    {Ω V : Type*} [Fintype Ω] (μ : Ω → ℝ) (bit : Ω → V → Bool)
    (hμ : ∑ ω, μ ω = 1) (v : V) :
    (∑ ω, ∑ ω', μ ω * μ ω' * if bit ω v = bit ω' v then (0 : ℝ) else 1) =
      2 * (∑ ω, μ ω * if bit ω v then (1 : ℝ) else 0) *
        (1 - ∑ ω, μ ω * if bit ω v then (1 : ℝ) else 0) := by
  let a : Ω → ℝ := fun ω => if bit ω v then 1 else 0
  have hdis : ∀ ω ω', (if bit ω v = bit ω' v then (0 : ℝ) else 1) =
      a ω + a ω' - 2 * a ω * a ω' := by
    intro ω ω'
    simpa [a] using pom_fiber_posterior_hamming_diversity_bool_disagree (bit ω v) (bit ω' v)
  let A : ℝ := ∑ ω, μ ω * a ω
  have hleft : (∑ ω, ∑ ω', μ ω * μ ω' * a ω) = A := by
    calc
      (∑ ω, ∑ ω', μ ω * μ ω' * a ω) = ∑ ω, μ ω * a ω := by
        apply Finset.sum_congr rfl
        intro ω _
        calc
          (∑ ω', μ ω * μ ω' * a ω) = μ ω * a ω * ∑ ω', μ ω' := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro ω' _
            ring
          _ = μ ω * a ω := by
            rw [hμ]
            ring
      _ = A := by
        rfl
  have hright : (∑ ω, ∑ ω', μ ω * μ ω' * a ω') = A := by
    calc
      (∑ ω, ∑ ω', μ ω * μ ω' * a ω') = ∑ ω, μ ω * A := by
        apply Finset.sum_congr rfl
        intro ω _
        calc
          (∑ ω', μ ω * μ ω' * a ω') = ∑ ω', μ ω * (μ ω' * a ω') := by
            apply Finset.sum_congr rfl
            intro ω' _
            ring
          _ = μ ω * (∑ ω', μ ω' * a ω') := by
            rw [Finset.mul_sum]
          _ = μ ω * A := by
            rw [show A = ∑ ω', μ ω' * a ω' by rfl]
      _ = A := by
        rw [← Finset.sum_mul, hμ]
        ring
  have hboth : (∑ ω, ∑ ω', μ ω * μ ω' * (2 * a ω * a ω')) = 2 * A * A := by
    calc
      (∑ ω, ∑ ω', μ ω * μ ω' * (2 * a ω * a ω')) =
          ∑ ω, μ ω * a ω * (2 * A) := by
        apply Finset.sum_congr rfl
        intro ω _
        calc
          (∑ ω', μ ω * μ ω' * (2 * a ω * a ω')) =
              ∑ ω', μ ω * a ω * (2 * (μ ω' * a ω')) := by
            apply Finset.sum_congr rfl
            intro ω' _
            ring
          _ = μ ω * a ω * (∑ ω', 2 * (μ ω' * a ω')) := by
            rw [Finset.mul_sum]
          _ = μ ω * a ω * (2 * A) := by
            congr 1
            rw [show A = ∑ ω', μ ω' * a ω' by rfl]
            rw [Finset.mul_sum]
      _ = 2 * A * A := by
        rw [← Finset.sum_mul]
        change A * (2 * A) = 2 * A * A
        ring
  have hexpand :
      (∑ ω, ∑ ω', μ ω * μ ω' * (a ω + a ω' - 2 * a ω * a ω')) =
        (∑ ω, ∑ ω', μ ω * μ ω' * a ω) +
          (∑ ω, ∑ ω', μ ω * μ ω' * a ω') -
            (∑ ω, ∑ ω', μ ω * μ ω' * (2 * a ω * a ω')) := by
    calc
      (∑ ω, ∑ ω', μ ω * μ ω' * (a ω + a ω' - 2 * a ω * a ω')) =
          ∑ ω, ∑ ω',
            (μ ω * μ ω' * a ω + μ ω * μ ω' * a ω' -
              μ ω * μ ω' * (2 * a ω * a ω')) := by
        apply Finset.sum_congr rfl
        intro ω _
        apply Finset.sum_congr rfl
        intro ω' _
        ring
      _ =
          (∑ ω, ∑ ω', μ ω * μ ω' * a ω) +
            (∑ ω, ∑ ω', μ ω * μ ω' * a ω') -
              (∑ ω, ∑ ω', μ ω * μ ω' * (2 * a ω * a ω')) := by
        simp [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp_rw [hdis]
  rw [hexpand, hleft, hright, hboth]
  change A + A - 2 * A * A = 2 * A * (1 - A)
  ring

theorem paper_pom_fiber_posterior_hamming_diversity {Ω V : Type*} [Fintype Ω] [Fintype V]
    (μ : Ω → ℝ) (bit : Ω → V → Bool) (hμ : ∑ ω, μ ω = 1) :
    let π : V → ℝ := fun v => ∑ ω, μ ω * if bit ω v then 1 else 0
    let hdist : Ω → Ω → ℝ :=
      fun ω ω' => 3 * ∑ v, if bit ω v = bit ω' v then 0 else 1
    (∑ ω, ∑ ω', μ ω * μ ω' * hdist ω ω') =
      6 * ∑ v, π v * (1 - π v) := by
  intro π hdist
  have hcoord :
      ∀ v,
        (∑ ω, ∑ ω', μ ω * μ ω' * if bit ω v = bit ω' v then (0 : ℝ) else 1) =
          2 * π v * (1 - π v) := by
    intro v
    simpa [π] using pom_fiber_posterior_hamming_diversity_coordinate μ bit hμ v
  calc
    (∑ ω, ∑ ω', μ ω * μ ω' * hdist ω ω') =
        ∑ ω, ∑ ω', ∑ v,
          3 * (μ ω * μ ω' *
            if bit ω v = bit ω' v then (0 : ℝ) else 1) := by
      simp [hdist, Finset.mul_sum, mul_assoc, mul_comm]
    _ =
        ∑ ω, ∑ v, ∑ ω',
          3 * (μ ω * μ ω' *
            if bit ω v = bit ω' v then (0 : ℝ) else 1) := by
      apply Finset.sum_congr rfl
      intro ω _
      rw [Finset.sum_comm]
    _ =
        ∑ v, ∑ ω, ∑ ω',
          3 * (μ ω * μ ω' *
            if bit ω v = bit ω' v then (0 : ℝ) else 1) := by
      rw [Finset.sum_comm]
    _ = 3 *
        ∑ v,
          ∑ ω, ∑ ω', μ ω * μ ω' *
            if bit ω v = bit ω' v then (0 : ℝ) else 1 := by
      simp [Finset.mul_sum, mul_assoc, mul_comm]
    _ = 3 * ∑ v, 2 * π v * (1 - π v) := by
      congr 1
      exact Finset.sum_congr rfl (fun v _ => hcoord v)
    _ = ∑ v, 6 * (π v * (1 - π v)) := by
      simp [Finset.mul_sum]
      ring
    _ = 6 * ∑ v, π v * (1 - π v) := by
      simp [Finset.mul_sum]

end Omega.POM
