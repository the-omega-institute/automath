import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Conclusion

noncomputable section

/-- The `j`-th Dirichlet edge pole `4π²(j+1)²`. -/
def conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_pole (j : ℕ) : ℝ :=
  4 * Real.pi ^ 2 * (j + 1 : ℝ) ^ 2

/-- The `j`-th Weierstrass factor of the diffusive-sinc edge model. -/
def conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_factor
    (j : ℕ) (u : ℝ) : ℝ :=
  1 - u / conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_pole j

/-- The truncated Weierstrass product for the edge-scaled kernel. -/
def conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_kernel :
    ℕ → ℝ → ℝ
  | 0, _ => 1
  | N + 1, u =>
      conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_kernel N u *
        conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_factor N u

/-- The truncated Dirichlet resolvent attached to the pole lattice. -/
def conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_resolvent :
    ℕ → ℝ → ℝ
  | 0, _ => 0
  | N + 1, u =>
      conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_resolvent N u -
        1 / (conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_pole N - u)

lemma conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_pole_ne_zero (j : ℕ) :
    conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_pole j ≠ 0 := by
  have h4 : (4 : ℝ) ≠ 0 := by norm_num
  have hpi : Real.pi ^ 2 ≠ 0 := by positivity
  have hj : (j + 1 : ℝ) ^ 2 ≠ 0 := by positivity
  exact mul_ne_zero (mul_ne_zero h4 hpi) hj

lemma conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_factor_eq
    (j : ℕ) (u : ℝ) :
    conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_factor j u =
      (conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_pole j - u) /
        conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_pole j := by
  rw [conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_factor]
  field_simp [conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_pole_ne_zero j]

lemma conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_resolvent_eq_sum
    (N : ℕ) (u : ℝ) :
    conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_resolvent N u =
      -((Finset.range N).sum fun j =>
          1 / (conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_pole j - u) ) := by
  induction N with
  | zero =>
      simp [conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_resolvent]
  | succ N ih =>
      rw [conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_resolvent, ih,
        Finset.sum_range_succ]
      ring

lemma conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_kernel_ne_zero
    (N : ℕ) (u : ℝ)
    (hu :
      ∀ j < N, u ≠ conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_pole j) :
    conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_kernel N u ≠ 0 := by
  induction N with
  | zero =>
      simp [conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_kernel]
  | succ N ih =>
      have huN :
          u ≠ conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_pole N := by
        exact hu N (Nat.lt_succ_self N)
      have htail :
          ∀ j < N, u ≠ conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_pole j := by
        intro j hj
        exact hu j (Nat.lt_trans hj (Nat.lt_succ_self N))
      have hk : conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_kernel N u ≠ 0 :=
        ih htail
      have hf :
          conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_factor N u ≠ 0 := by
        rw [conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_factor_eq]
        exact div_ne_zero (sub_ne_zero.mpr (Ne.symm huN))
          (conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_pole_ne_zero N)
      simp [conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_kernel, hk, hf]

lemma conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_kernel_hasDerivAt
    (N : ℕ) (u : ℝ)
    (hu :
      ∀ j < N, u ≠ conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_pole j) :
    HasDerivAt
      (fun x => conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_kernel N x)
      (conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_kernel N u *
        conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_resolvent N u)
      u := by
  induction N with
  | zero =>
      simpa [conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_kernel,
        conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_resolvent] using
        (hasDerivAt_const u (1 : ℝ))
  | succ N ih =>
      have huN :
          u ≠ conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_pole N := by
        exact hu N (Nat.lt_succ_self N)
      have htail :
          ∀ j < N, u ≠ conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_pole j := by
        intro j hj
        exact hu j (Nat.lt_trans hj (Nat.lt_succ_self N))
      have hk :=
        ih htail
      have hf :
          HasDerivAt
            (fun x =>
              conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_factor N x)
            (-(conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_pole N)⁻¹) u := by
        simpa [conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_factor, div_eq_mul_inv,
          sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm]
          using (hasDerivAt_id u).const_mul
            (-(conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_pole N)⁻¹)
      have hprod :
          HasDerivAt
            (fun x =>
              conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_kernel N x *
                conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_factor N x)
            (conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_kernel N u *
                conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_resolvent N u *
                conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_factor N u +
              conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_kernel N u *
                (-(conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_pole N)⁻¹))
            u := hk.mul hf
      have hvalue :
          conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_kernel (N + 1) u *
              conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_resolvent (N + 1) u =
            conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_kernel N u *
                  conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_resolvent N u *
                conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_factor N u +
              conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_kernel N u *
                (-(conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_pole N)⁻¹) := by
        have hpole :=
          conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_pole_ne_zero N
        have hsub :
            conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_pole N - u ≠ 0 := by
          exact sub_ne_zero.mpr (Ne.symm huN)
        have hfactor :
            conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_factor N u *
                (-(1 / (conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_pole N - u))) =
              -(conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_pole N)⁻¹ := by
          rw [conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_factor_eq]
          field_simp [hpole, hsub]
        calc
          conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_kernel (N + 1) u *
              conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_resolvent (N + 1) u =
            conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_kernel N u *
                conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_factor N u *
                (conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_resolvent N u -
                  1 / (conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_pole N - u)) := by
              simp [conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_kernel,
                conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_resolvent]
          _ = conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_kernel N u *
                  conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_resolvent N u *
                  conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_factor N u +
                conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_kernel N u *
                  (conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_factor N u *
                    (-(1 / (conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_pole N - u)))) := by
              ring
          _ = conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_kernel N u *
                  conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_resolvent N u *
                  conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_factor N u +
                conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_kernel N u *
                  (-(conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_pole N)⁻¹) := by
              rw [hfactor]
      change HasDerivAt
        (fun x =>
          conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_kernel N x *
            conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_factor N x)
        (conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_kernel (N + 1) u *
          conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_resolvent (N + 1) u)
        u
      convert hprod using 1

/-- Paper label: `thm:conclusion-leyang-edge-log-derivative-dirichlet-resolvent-limit`.
For the truncated diffusive-sinc Weierstrass product, avoiding the first `N` pole locations forces
nonvanishing, so the logarithmic derivative is well defined and equals the truncated Dirichlet
resolvent `-∑_{j < N} 1 / (4π²(j+1)² - u)`. -/
theorem paper_conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit
    (N : ℕ) {u : ℝ}
    (hu :
      ∀ j < N, u ≠ conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_pole j) :
    conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_kernel N u ≠ 0 ∧
      HasDerivAt
        (fun x =>
          Real.log (conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_kernel N x))
        (conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_resolvent N u)
        u ∧
      conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_resolvent N u =
        -((Finset.range N).sum fun j =>
            1 / (conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_pole j - u) ) := by
  have hne :=
    conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_kernel_ne_zero N u hu
  have hderiv :=
    conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_kernel_hasDerivAt N u hu
  have hlog := hderiv.log hne
  refine ⟨hne, ?_, conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_resolvent_eq_sum N u⟩
  have hquot :
      conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_kernel N u *
          conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_resolvent N u /
        conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_kernel N u =
        conclusion_leyang_edge_log_derivative_dirichlet_resolvent_limit_resolvent N u := by
    field_simp [hne]
  simpa [hquot] using hlog

end

end Omega.Conclusion
