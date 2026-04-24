import Mathlib.Tactic
import Omega.Zeta.XiTimePart64baFoldMultiplicityMajorizationBalancing

open scoped BigOperators

namespace Omega.Zeta

private lemma xi_time_part9xaa_wulff_schur_minimal_spectrum_sum_indicator_range
    (N r : ℕ) (hr : r ≤ N) :
    Finset.sum (Finset.range N) (fun i => if i < r then 1 else 0) = r := by
  calc
    Finset.sum (Finset.range N) (fun i => if i < r then 1 else 0)
        = Finset.sum ((Finset.range N).filter (fun i => i < r)) (fun _ => 1) := by
            rw [Finset.sum_filter]
    _ = ((Finset.range N).filter (fun i => i < r)).card := by
          rw [Finset.card_eq_sum_ones]
    _ = (Finset.range r).card := by
          have hEq : (Finset.range N).filter (fun i => i < r) = Finset.range r := by
            ext i
            constructor
            · intro hi
              exact Finset.mem_range.mpr ((Finset.mem_filter.mp hi).2)
            · intro hi
              exact Finset.mem_filter.mpr
                ⟨Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hi) hr),
                  Finset.mem_range.mp hi⟩
          rw [hEq]
    _ = r := by simp

private lemma xi_time_part9xaa_wulff_schur_minimal_spectrum_balanced_sum
    {F M : ℕ} (hF : 0 < F) :
    ∑ i : Fin F, xiTimePart64baBalancedProfile F M i = M := by
  let q := M / F
  let r := M % F
  have hcount : Finset.sum (Finset.range F) (fun i => if i < r then 1 else 0) = r := by
    exact xi_time_part9xaa_wulff_schur_minimal_spectrum_sum_indicator_range F r (by
      have hrlt : M % F < F := Nat.mod_lt _ hF
      exact le_of_lt hrlt)
  calc
    ∑ i, xiTimePart64baBalancedProfile F M i = ∑ i : Fin F, (q + if i.1 < r then 1 else 0) := by
      simp [xiTimePart64baBalancedProfile, q, r]
    _ = (∑ i : Fin F, q) + (∑ i : Fin F, (if i.1 < r then 1 else 0)) := by
      rw [Finset.sum_add_distrib]
    _ = F * q + r := by
      have hsumInd : (∑ i : Fin F, (if i.1 < r then 1 else 0)) = r := by
        exact (Fin.sum_univ_eq_sum_range (fun i : ℕ => if i < r then 1 else 0) F).trans hcount
      rw [hsumInd]
      simp
    _ = M := by
      exact Nat.div_add_mod M F

private lemma xi_time_part9xaa_wulff_schur_minimal_spectrum_int_sq_ge (z : ℤ) :
    z ^ 2 ≥ z := by
  nlinarith [sq_nonneg (z - 1)]

/-- `thm:xi-time-part9xaa-wulff-schur-minimal-spectrum` -/
theorem paper_xi_time_part9xaa_wulff_schur_minimal_spectrum {F M : ℕ} (hF : 0 < F)
    (d : Fin F → ℕ) (hpos : ∀ i, 1 ≤ d i) (hsum : ∑ i, d i = M) :
    let b := Omega.Zeta.xiTimePart64baBalancedProfile F M
    (∀ i, b i = M / F ∨ b i = M / F + 1) ∧
      (∑ i, b i = M) ∧
      (∑ i, (b i : ℝ)^2 ≤ ∑ i, (d i : ℝ)^2) := by
  let b := Omega.Zeta.xiTimePart64baBalancedProfile F M
  let q := M / F
  let r := M % F
  have _hM_ge : F ≤ M := by
    calc
      F = ∑ i : Fin F, (1 : ℕ) := by simp
      _ ≤ ∑ i, d i := by
            exact Finset.sum_le_sum fun i _ => hpos i
      _ = M := hsum
  have hbal :=
    paper_xi_time_part64ba_fold_multiplicity_majorization_balancing (F := F) (M := M)
  rcases hbal with ⟨_, hvals, _, _, _⟩
  have hsum_b : ∑ i, b i = M := by
    simpa [b, q, r] using
      xi_time_part9xaa_wulff_schur_minimal_spectrum_balanced_sum (F := F) (M := M) hF
  have hcount_nat : Finset.sum (Finset.range F) (fun i => if i < r then 1 else 0) = r := by
    exact xi_time_part9xaa_wulff_schur_minimal_spectrum_sum_indicator_range F r (by
      have hrlt : M % F < F := Nat.mod_lt _ hF
      exact le_of_lt hrlt)
  have hcount_int : ∑ i : Fin F, (if i.1 < r then (1 : ℤ) else 0) = r := by
    exact_mod_cast
      ((Fin.sum_univ_eq_sum_range (fun i : ℕ => if i < r then (1 : ℕ) else 0) F).trans hcount_nat)
  have hsumz : ∑ i, (d i : ℤ) = M := by
    exact_mod_cast hsum
  have hsum_const_q : ∑ i : Fin F, (q : ℤ) = F * q := by
    simp [q]
  have hsum_const_qsq : ∑ i : Fin F, ((q : ℤ) ^ 2) = F * q ^ 2 := by
    simp [q]
  have hb_centered : ∑ i, ((b i : ℤ) - q) = r := by
    calc
      ∑ i, ((b i : ℤ) - q) = ∑ i : Fin F, (if i.1 < r then (1 : ℤ) else 0) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [b, q, r, xiTimePart64baBalancedProfile]
      _ = r := hcount_int
  have hd_centered : ∑ i, ((d i : ℤ) - q) = r := by
    calc
      ∑ i, ((d i : ℤ) - q) = (∑ i, (d i : ℤ)) - ∑ i : Fin F, (q : ℤ) := by
        rw [Finset.sum_sub_distrib]
      _ = M - F * q := by
        rw [hsumz, hsum_const_q]
      _ = r := by
        have hdecomp : (F : ℤ) * q + r = M := by
          exact_mod_cast (Nat.div_add_mod M F)
        linarith
  have hd_sq_lower : (r : ℤ) ≤ ∑ i, ((d i : ℤ) - q) ^ 2 := by
    calc
      (r : ℤ) = ∑ i, ((d i : ℤ) - q) := by
        simpa using hd_centered.symm
      _ ≤ ∑ i, ((d i : ℤ) - q) ^ 2 := by
        exact Finset.sum_le_sum fun i _ =>
          xi_time_part9xaa_wulff_schur_minimal_spectrum_int_sq_ge ((d i : ℤ) - q)
  have hb_sq_formula : ∑ i, (b i : ℤ) ^ 2 = (F : ℤ) * q ^ 2 + (2 * q + 1) * r := by
    calc
      ∑ i, (b i : ℤ) ^ 2 = ∑ i, (((b i : ℤ) - q) ^ 2 + 2 * q * ((b i : ℤ) - q) + q ^ 2) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = ∑ i, ((b i : ℤ) - q) ^ 2 + ∑ i, (2 * q * ((b i : ℤ) - q)) + ∑ i, ((q : ℤ) ^ 2) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      _ = ∑ i, ((b i : ℤ) - q) ^ 2 + (2 * q) * r + (F : ℤ) * q ^ 2 := by
        rw [show (∑ i, 2 * q * ((b i : ℤ) - q)) = (2 * q) * (∑ i, ((b i : ℤ) - q)) by
          rw [Finset.mul_sum]]
        rw [hb_centered, hsum_const_qsq]
      _ = (F : ℤ) * q ^ 2 + (2 * q + 1) * r := by
        have hcenter_sq : ∑ i, ((b i : ℤ) - q) ^ 2 = r := by
          calc
            ∑ i, ((b i : ℤ) - q) ^ 2 = ∑ i : Fin F, (if i.1 < r then (1 : ℤ) else 0) := by
              apply Finset.sum_congr rfl
              intro i hi
              split_ifs <;> simp [b, q, r, xiTimePart64baBalancedProfile, *]
            _ = r := hcount_int
        rw [hcenter_sq]
        ring
  have hd_sq_formula_lower : (F : ℤ) * q ^ 2 + (2 * q + 1) * r ≤ ∑ i, (d i : ℤ) ^ 2 := by
    have hexpand :
        ∑ i, (d i : ℤ) ^ 2 = ∑ i, ((d i : ℤ) - q) ^ 2 + (2 * q) * r + (F : ℤ) * q ^ 2 := by
      calc
        ∑ i, (d i : ℤ) ^ 2 = ∑ i, (((d i : ℤ) - q) ^ 2 + 2 * q * ((d i : ℤ) - q) + q ^ 2) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = ∑ i, ((d i : ℤ) - q) ^ 2 + ∑ i, (2 * q * ((d i : ℤ) - q)) + ∑ i, ((q : ℤ) ^ 2) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
        _ = ∑ i, ((d i : ℤ) - q) ^ 2 + (2 * q) * r + (F : ℤ) * q ^ 2 := by
          rw [show (∑ i, 2 * q * ((d i : ℤ) - q)) = (2 * q) * (∑ i, ((d i : ℤ) - q)) by
            rw [Finset.mul_sum]]
          rw [hd_centered, hsum_const_qsq]
    have hmain :
        (F : ℤ) * q ^ 2 + (2 * q + 1) * r ≤
          ∑ i, ((d i : ℤ) - q) ^ 2 + (2 * q) * r + (F : ℤ) * q ^ 2 := by
      linarith
    rw [hexpand]
    exact hmain
  refine ⟨?_, hsum_b, ?_⟩
  · simpa [b, q, r] using hvals
  · have hb_sq_le : ∑ i, (b i : ℤ) ^ 2 ≤ ∑ i, (d i : ℤ) ^ 2 := by
      rw [hb_sq_formula]
      exact hd_sq_formula_lower
    exact_mod_cast hb_sq_le

end Omega.Zeta
