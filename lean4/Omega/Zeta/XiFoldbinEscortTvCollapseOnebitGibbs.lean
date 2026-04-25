import Mathlib.Analysis.SpecificLimits.Fibonacci
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Real.GoldenRatio

namespace Omega.Zeta

open Filter Real
open scoped Topology goldenRatio

/-- Exact last-bit partition sizes in the bin-fold model. -/
def xi_foldbin_escort_tv_collapse_onebit_gibbs_lastbit_count (m : ℕ) : Bool → ℕ
  | false => Nat.fib (m + 1)
  | true => Nat.fib m

/-- Finite-scale Bernoulli weight carried by the last-bit-`1` block. -/
noncomputable def xi_foldbin_escort_tv_collapse_onebit_gibbs_theta (m : ℕ) : ℝ :=
  (Nat.fib m : ℝ) / Nat.fib (m + 2)

/-- Limiting one-bit Gibbs weight at escort temperature `q`. -/
noncomputable def xi_foldbin_escort_tv_collapse_onebit_gibbs_gibbs_theta (q : ℝ) : ℝ :=
  1 / (1 + Real.goldenRatio ^ (q + 1))

/-- Bernoulli law with mass `θ` on the last-bit-`1` block. -/
def xi_foldbin_escort_tv_collapse_onebit_gibbs_blockLaw (θ : ℝ) : Bool → ℝ
  | false => 1 - θ
  | true => θ

/-- Total-variation distance on the two-point last-bit space. -/
noncomputable def xi_foldbin_escort_tv_collapse_onebit_gibbs_tvDistance
    (p q : Bool → ℝ) : ℝ :=
  (|p false - q false| + |p true - q true|) / 2

private lemma xi_foldbin_escort_tv_collapse_onebit_gibbs_tv_blockLaw (a b : ℝ) :
    xi_foldbin_escort_tv_collapse_onebit_gibbs_tvDistance
        (xi_foldbin_escort_tv_collapse_onebit_gibbs_blockLaw a)
        (xi_foldbin_escort_tv_collapse_onebit_gibbs_blockLaw b) =
      |a - b| := by
  unfold xi_foldbin_escort_tv_collapse_onebit_gibbs_tvDistance
    xi_foldbin_escort_tv_collapse_onebit_gibbs_blockLaw
  have hfalse : (1 - a) - (1 - b) = -(a - b) := by ring
  rw [hfalse, abs_neg]
  ring

/-- Paper label: `thm:xi-foldbin-escort-tv-collapse-onebit-gibbs`.
The exact last-bit blocks have Fibonacci sizes `F_{m+1}` and `F_m`; the resulting Bernoulli weight
on the last-bit-`1` block is `F_m / F_{m+2}` and its two-point law collapses in total variation to
the limiting Bernoulli law with parameter `φ⁻²`; the one-bit Gibbs parameter is
`θ(q) = 1 / (1 + φ^(q+1))`; and the Fibonacci ratio tends to `φ`. -/
def xi_foldbin_escort_tv_collapse_onebit_gibbs_statement : Prop :=
  (∀ m, xi_foldbin_escort_tv_collapse_onebit_gibbs_lastbit_count m false = Nat.fib (m + 1)) ∧
    (∀ m, xi_foldbin_escort_tv_collapse_onebit_gibbs_lastbit_count m true = Nat.fib m) ∧
    Tendsto
      (fun m : ℕ =>
        xi_foldbin_escort_tv_collapse_onebit_gibbs_tvDistance
          (xi_foldbin_escort_tv_collapse_onebit_gibbs_blockLaw
            (xi_foldbin_escort_tv_collapse_onebit_gibbs_theta m))
          (xi_foldbin_escort_tv_collapse_onebit_gibbs_blockLaw
            (Real.goldenRatio⁻¹ * Real.goldenRatio⁻¹)))
      atTop (nhds 0) ∧
    (∀ q : ℝ,
      xi_foldbin_escort_tv_collapse_onebit_gibbs_gibbs_theta q =
        1 / (1 + Real.goldenRatio ^ (q + 1))) ∧
    Tendsto (fun m : ℕ => (Nat.fib (m + 1) : ℝ) / Nat.fib m) atTop (nhds Real.goldenRatio)

theorem paper_xi_foldbin_escort_tv_collapse_onebit_gibbs :
    xi_foldbin_escort_tv_collapse_onebit_gibbs_statement := by
  let thetaInf : ℝ := Real.goldenRatio⁻¹ * Real.goldenRatio⁻¹
  have hphiinv : (Real.goldenRatio⁻¹ : ℝ) = (-ψ : ℝ) := by
    simpa using (Real.inv_goldenRatio : (Real.goldenRatio⁻¹ : ℝ) = (-ψ : ℝ))
  have hratio_inv :
      Tendsto (fun m : ℕ => (Nat.fib m : ℝ) / Nat.fib (m + 1)) atTop
        (nhds (Real.goldenRatio⁻¹)) := by
    rw [hphiinv]
    exact tendsto_fib_div_fib_succ_atTop
  have hratio_inv_shift :
      Tendsto (fun m : ℕ => (Nat.fib (m + 1) : ℝ) / Nat.fib (m + 2)) atTop
        (nhds (Real.goldenRatio⁻¹)) := by
    rw [hphiinv]
    simpa [Nat.add_assoc] using (tendsto_fib_div_fib_succ_atTop.comp (tendsto_add_atTop_nat 1))
  have htheta :
      Tendsto (fun m : ℕ => xi_foldbin_escort_tv_collapse_onebit_gibbs_theta m) atTop
        (nhds thetaInf) := by
    have hmul := hratio_inv.mul hratio_inv_shift
    have hEq :
        (fun m : ℕ =>
          (Nat.fib m : ℝ) / Nat.fib (m + 1) * ((Nat.fib (m + 1) : ℝ) / Nat.fib (m + 2))) =
          xi_foldbin_escort_tv_collapse_onebit_gibbs_theta := by
      funext m
      have hfib1_nat : Nat.fib (m + 1) ≠ 0 := Nat.ne_of_gt (Nat.fib_pos.mpr (Nat.succ_pos _))
      have hfib2_nat : Nat.fib (m + 2) ≠ 0 := Nat.ne_of_gt (Nat.fib_pos.mpr (Nat.succ_pos _))
      have hfib1 : (Nat.fib (m + 1) : ℝ) ≠ 0 := by exact_mod_cast hfib1_nat
      have hfib2 : (Nat.fib (m + 2) : ℝ) ≠ 0 := by exact_mod_cast hfib2_nat
      unfold xi_foldbin_escort_tv_collapse_onebit_gibbs_theta
      field_simp [hfib1, hfib2]
    simpa [hEq, thetaInf] using hmul
  have htv :
      Tendsto
        (fun m : ℕ =>
          xi_foldbin_escort_tv_collapse_onebit_gibbs_tvDistance
            (xi_foldbin_escort_tv_collapse_onebit_gibbs_blockLaw
              (xi_foldbin_escort_tv_collapse_onebit_gibbs_theta m))
            (xi_foldbin_escort_tv_collapse_onebit_gibbs_blockLaw
              thetaInf))
        atTop (nhds 0) := by
    have hsub :
        Tendsto
          (fun m : ℕ => xi_foldbin_escort_tv_collapse_onebit_gibbs_theta m - thetaInf) atTop
          (nhds (thetaInf - thetaInf)) :=
      htheta.sub tendsto_const_nhds
    have habs :
        Tendsto
          (fun m : ℕ => |xi_foldbin_escort_tv_collapse_onebit_gibbs_theta m - thetaInf|) atTop
          (nhds |thetaInf - thetaInf|) := by
      simpa using hsub.abs
    simpa [thetaInf, xi_foldbin_escort_tv_collapse_onebit_gibbs_tv_blockLaw] using habs
  refine ⟨fun _ => rfl, fun _ => rfl, htv, ?_, tendsto_fib_succ_div_fib_atTop⟩
  intro q
  rfl

end Omega.Zeta
