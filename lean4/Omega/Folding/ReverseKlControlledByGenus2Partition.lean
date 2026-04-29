import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic
import Omega.Folding.Fiber
import Omega.POM.ReverseKlBoundByDispersion

namespace Omega.Folding

open scoped BigOperators

noncomputable section

/-- The fold pushforward `w_m(x) = d_m(x) / 2^m`. -/
def fold_reversekl_controlled_by_genus2_partition_pushforward (m : ℕ) : Omega.X m → ℝ :=
  fun x => Omega.X.fiberMultiplicity x / (2 ^ m : ℕ)

/-- The genus-2 partition function `Z_m(Σ₂) = ∑_x d_m(x)⁻²`. -/
def fold_reversekl_controlled_by_genus2_partition_genus2 (m : ℕ) : ℝ :=
  ∑ x : Omega.X m, ((Omega.X.fiberMultiplicity x : ℝ)⁻¹) ^ (2 : ℕ)

/-- Paper label: `cor:fold-reversekl-controlled-by-genus2-partition`.
Applying the reverse-KL-by-dispersion bound to the fold pushforward and then Cauchy--Schwarz to
`∑ d_m(x)⁻¹` yields the genus-`2` control
`D_KL(U_m || w_m) ≤ m log 2 - (3/2) log |X_m| + (1/2) log Z_m(Σ₂)`. -/
theorem paper_fold_reversekl_controlled_by_genus2_partition (m : ℕ) :
    (∑ x : Omega.X m,
        ((Fintype.card (Omega.X m) : ℝ)⁻¹) *
          Real.log
            (((Fintype.card (Omega.X m) : ℝ)⁻¹) /
              (fold_reversekl_controlled_by_genus2_partition_pushforward m x))) ≤
      m * Real.log 2 - (3 / 2 : ℝ) * Real.log (Fintype.card (Omega.X m)) +
        (1 / 2 : ℝ) * Real.log (fold_reversekl_controlled_by_genus2_partition_genus2 m) := by
  classical
  let w := fold_reversekl_controlled_by_genus2_partition_pushforward m
  let Z := fold_reversekl_controlled_by_genus2_partition_genus2 m
  let n : ℝ := Fintype.card (Omega.X m)
  let A : ℝ := ∑ x : Omega.X m, (Omega.X.fiberMultiplicity x : ℝ)⁻¹
  have hcard_nat : 0 < Fintype.card (Omega.X m) := by
    rw [Omega.X.card_eq_fib]
    exact Nat.fib_pos.mpr (by omega)
  letI : Nonempty (Omega.X m) := Fintype.card_pos_iff.mp hcard_nat
  have hn_pos : 0 < n := by
    simpa [n] using (show (0 : ℝ) < (Fintype.card (Omega.X m) : ℝ) by exact_mod_cast hcard_nat)
  have hn_ne : n ≠ 0 := ne_of_gt hn_pos
  have hpow_pos : 0 < (2 : ℝ) ^ m := by positivity
  have hpow_ne : (2 : ℝ) ^ m ≠ 0 := ne_of_gt hpow_pos
  have hw_pos : ∀ x : Omega.X m, 0 < w x := by
    intro x
    exact div_pos (by exact_mod_cast Omega.X.fiberMultiplicity_pos x) (by positivity)
  have hw_sum : ∑ x : Omega.X m, w x = 1 := by
    calc
      ∑ x : Omega.X m, w x =
          (∑ x : Omega.X m, Omega.X.fiberMultiplicity x) / (2 ^ m : ℕ) := by
            simp [w, fold_reversekl_controlled_by_genus2_partition_pushforward, Finset.sum_div]
      _ = ((2 ^ m : ℕ) : ℝ) / (2 ^ m : ℕ) := by
        congr 1
        exact_mod_cast Omega.X.fiberMultiplicity_sum_eq_pow m
      _ = 1 := by
        field_simp [show ((2 ^ m : ℕ) : ℝ) ≠ 0 by positivity]
  have hdisp :=
    Omega.POM.paper_pom_reverse_kl_bound_by_dispersion w hw_pos hw_sum
  have hA_nonneg : 0 ≤ A := by
    exact Finset.sum_nonneg (fun x _ => inv_nonneg.mpr (by positivity : 0 ≤ (Omega.X.fiberMultiplicity x : ℝ)))
  have hA_pos : 0 < A := by
    classical
    obtain ⟨x0⟩ := (show Nonempty (Omega.X m) from inferInstance)
    have hx0 : 0 < (Omega.X.fiberMultiplicity x0 : ℝ)⁻¹ := by
      exact inv_pos.mpr (by exact_mod_cast Omega.X.fiberMultiplicity_pos x0)
    have hle :
        (Omega.X.fiberMultiplicity x0 : ℝ)⁻¹ ≤
          ∑ x : Omega.X m, (Omega.X.fiberMultiplicity x : ℝ)⁻¹ := by
      exact Finset.single_le_sum
        (fun x _ => inv_nonneg.mpr (by positivity : 0 ≤ (Omega.X.fiberMultiplicity x : ℝ)))
        (Finset.mem_univ x0)
    exact lt_of_lt_of_le hx0 hle
  have hcs :
      A ^ (2 : ℕ) ≤ n * Z := by
    simpa [A, Z, fold_reversekl_controlled_by_genus2_partition_genus2, Finset.card_univ] using
      (sq_sum_le_card_mul_sum_sq
        (s := (Finset.univ : Finset (Omega.X m)))
        (f := fun x : Omega.X m => (Omega.X.fiberMultiplicity x : ℝ)⁻¹))
  have hZ_pos : 0 < Z := by
    have hA_sq_pos : 0 < A ^ (2 : ℕ) := by
      exact sq_pos_of_pos hA_pos
    by_contra hZ
    have hZ_le : Z ≤ 0 := le_of_not_gt hZ
    have hnZ_le : n * Z ≤ 0 := by
      exact mul_nonpos_of_nonneg_of_nonpos hn_pos.le hZ_le
    linarith
  have hlogA :
      Real.log A ≤ (Real.log n + Real.log Z) / 2 := by
    have hlogsq : Real.log (A ^ (2 : ℕ)) ≤ Real.log (n * Z) := by
      exact Real.log_le_log (by positivity) hcs
    rw [pow_two, Real.log_mul hA_pos.ne' hA_pos.ne'] at hlogsq
    rw [Real.log_mul hn_ne hZ_pos.ne'] at hlogsq
    linarith
  have hrhs_eq :
      Real.log ((n⁻¹ ^ (2 : ℕ)) * ∑ x : Omega.X m, (w x)⁻¹) =
        m * Real.log 2 - (2 : ℝ) * Real.log n + Real.log A := by
    have hsum_inv :
        ∑ x : Omega.X m, (w x)⁻¹ = (2 : ℝ) ^ m * A := by
      calc
        ∑ x : Omega.X m, (w x)⁻¹ =
            ∑ x : Omega.X m, ((2 : ℝ) ^ m) * (Omega.X.fiberMultiplicity x : ℝ)⁻¹ := by
              refine Finset.sum_congr rfl ?_
              intro x hx
              have hxne : (Omega.X.fiberMultiplicity x : ℝ) ≠ 0 := by
                exact_mod_cast Nat.ne_of_gt (Omega.X.fiberMultiplicity_pos x)
              have hpow_cast : (((2 ^ m : ℕ) : ℝ)) = (2 : ℝ) ^ m := by
                exact_mod_cast (show 2 ^ m = 2 ^ m by rfl)
              dsimp [w, fold_reversekl_controlled_by_genus2_partition_pushforward]
              rw [hpow_cast]
              field_simp [hpow_ne, hxne]
        _ = (2 : ℝ) ^ m * A := by
              rw [Finset.mul_sum]
    have hlog_inv_sq : Real.log (n⁻¹ ^ (2 : ℕ)) = (-2 : ℝ) * Real.log n := by
      rw [pow_two, Real.log_mul (inv_ne_zero hn_ne) (inv_ne_zero hn_ne)]
      rw [Real.log_inv n]
      ring
    have hlog_two_pow : Real.log ((2 : ℝ) ^ m) = m * Real.log 2 := by
      simpa using Real.log_pow (2 : ℝ) m
    calc
      Real.log ((n⁻¹ ^ (2 : ℕ)) * ∑ x : Omega.X m, (w x)⁻¹)
          = Real.log (n⁻¹ ^ (2 : ℕ)) + Real.log (∑ x : Omega.X m, (w x)⁻¹) := by
              rw [Real.log_mul (by positivity) (ne_of_gt (by simpa [hsum_inv] using mul_pos hpow_pos hA_pos))]
      _ = Real.log (n⁻¹ ^ (2 : ℕ)) + Real.log ((2 : ℝ) ^ m * A) := by rw [hsum_inv]
      _ = Real.log (n⁻¹ ^ (2 : ℕ)) + (Real.log ((2 : ℝ) ^ m) + Real.log A) := by
              rw [Real.log_mul hpow_ne hA_pos.ne']
      _ = (-2 : ℝ) * Real.log n + (m * Real.log 2 + Real.log A) := by
              rw [hlog_inv_sq, hlog_two_pow]
      _ = m * Real.log 2 - (2 : ℝ) * Real.log n + Real.log A := by ring
  calc
    (∑ x : Omega.X m, ((Fintype.card (Omega.X m) : ℝ)⁻¹) *
        Real.log (((Fintype.card (Omega.X m) : ℝ)⁻¹) / w x))
        ≤ Real.log ((((Fintype.card (Omega.X m) : ℝ)⁻¹) ^ (2 : ℕ)) * ∑ x : Omega.X m, (w x)⁻¹) :=
      hdisp
    _ = m * Real.log 2 - (2 : ℝ) * Real.log n + Real.log A := by
      simpa [n] using hrhs_eq
    _ ≤ m * Real.log 2 - (3 / 2 : ℝ) * Real.log n + (1 / 2 : ℝ) * Real.log Z := by
      linarith
    _ = m * Real.log 2 - (3 / 2 : ℝ) * Real.log (Fintype.card (Omega.X m)) +
          (1 / 2 : ℝ) * Real.log Z := by
      rfl
    _ = m * Real.log 2 - (3 / 2 : ℝ) * Real.log (Fintype.card (Omega.X m)) +
          (1 / 2 : ℝ) * Real.log (fold_reversekl_controlled_by_genus2_partition_genus2 m) := by
      rfl

end

end Omega.Folding
