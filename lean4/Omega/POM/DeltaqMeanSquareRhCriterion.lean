import Mathlib

namespace Omega.POM

noncomputable section

/-- The model weighted trace term `exp(δ_q (n+1))`, corresponding to a top-modulus contribution of
size `exp(δ_q n)` after the Perron normalization. -/
def deltaqSeriesTerm (δq : ℝ) (n : ℕ) : ℝ :=
  Real.exp (δq * (n + 1))

/-- The weighted partial sums appearing in the mean-square criterion. -/
def deltaqPartialSum (δq : ℝ) (N : ℕ) : ℝ :=
  (Finset.Icc 1 N).sum fun n => Real.exp (δq * (n : ℝ))

/-- Subcritical regime: the weighted series is summable. -/
def subcriticalSummable : Prop :=
  ∀ δq, δq < 0 → Summable (deltaqSeriesTerm δq)

/-- Critical regime: the weighted partial sums grow linearly. -/
def criticalLinear : Prop :=
  ∀ N : ℕ, deltaqPartialSum 0 N = N

/-- Supercritical regime: the weighted partial sums admit explicit exponential lower and upper
bounds. -/
def supercriticalExponential : Prop :=
  ∀ δq, 0 < δq → ∀ N : ℕ, 1 ≤ N →
    Real.exp (δq * (N : ℝ)) ≤ deltaqPartialSum δq N ∧
      deltaqPartialSum δq N ≤ N * Real.exp (δq * (N : ℝ))

private lemma deltaqSeriesTerm_eq_geometric (δq : ℝ) :
    deltaqSeriesTerm δq = fun n => Real.exp δq * (Real.exp δq) ^ n := by
  funext n
  dsimp [deltaqSeriesTerm]
  have hsplit : δq * (n + 1 : ℝ) = δq + δq * n := by
    ring
  rw [hsplit, Real.exp_add, mul_comm (δq : ℝ) n, Real.exp_nat_mul]

private lemma subcritical_deltaq_summable (δq : ℝ) (hδq : δq < 0) :
    Summable (deltaqSeriesTerm δq) := by
  rw [deltaqSeriesTerm_eq_geometric]
  have hratio : Real.exp δq < 1 := Real.exp_lt_one_iff.mpr hδq
  simpa using (summable_geometric_of_lt_one (by positivity) hratio).mul_left (Real.exp δq)

private lemma critical_deltaq_partial_sum (N : ℕ) :
    deltaqPartialSum 0 N = N := by
  simp [deltaqPartialSum]

private lemma supercritical_deltaq_lower (δq : ℝ) (_hδq : 0 < δq) (N : ℕ) (hN : 1 ≤ N) :
    Real.exp (δq * (N : ℝ)) ≤ deltaqPartialSum δq N := by
  have hmem : N ∈ Finset.Icc 1 N := by
    simp [hN]
  have hsingle :
      Real.exp (δq * (N : ℝ)) ≤
        (Finset.Icc 1 N).sum (fun n : ℕ => Real.exp (δq * (n : ℝ))) := by
    exact Finset.single_le_sum
      (f := fun n : ℕ => Real.exp (δq * (n : ℝ)))
      (fun n _ => le_of_lt (Real.exp_pos (δq * (n : ℝ))))
      hmem
  simpa [deltaqPartialSum] using hsingle

private lemma supercritical_deltaq_upper (δq : ℝ) (hδq : 0 < δq) (N : ℕ) :
    deltaqPartialSum δq N ≤ N * Real.exp (δq * (N : ℝ)) := by
  calc
    deltaqPartialSum δq N = (Finset.Icc 1 N).sum (fun n => Real.exp (δq * (n : ℝ))) := by
      rfl
    _ ≤ (Finset.Icc 1 N).sum (fun _ => Real.exp (δq * (N : ℝ))) := by
      refine Finset.sum_le_sum ?_
      intro n hn
      have hn_le : n ≤ N := (Finset.mem_Icc.mp hn).2
      have hreal : (n : ℝ) ≤ N := by
        exact_mod_cast hn_le
      have hmul : δq * (n : ℝ) ≤ δq * (N : ℝ) := by
        nlinarith
      exact Real.exp_le_exp.mpr hmul
    _ = (Finset.card (Finset.Icc 1 N) : ℝ) * Real.exp (δq * (N : ℝ)) := by
      simp
    _ = N * Real.exp (δq * (N : ℝ)) := by
      simp

/-- Paper label: `thm:pom-deltaq-mean-square-rh-criterion`.

The weighted geometric model already exhibits the paper's three RH-style regimes: strict
subcritical summability, exact linear growth at the critical line, and exponential lower/upper
bounds above the line. -/
theorem paper_pom_deltaq_mean_square_rh_criterion :
    subcriticalSummable ∧ criticalLinear ∧ supercriticalExponential := by
  refine ⟨?_, ?_, ?_⟩
  · intro δq hδq
    exact subcritical_deltaq_summable δq hδq
  · intro N
    exact critical_deltaq_partial_sum N
  · intro δq hδq N hN
    exact ⟨supercritical_deltaq_lower δq hδq N hN, supercritical_deltaq_upper δq hδq N⟩

end

end Omega.POM
