import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

/-- The half-density mass `A_{1/2}(w) = Σ_x √(w x)`. -/
noncomputable def pom_diagonal_rate_critical_line_laplacian_first_order_A {k : ℕ}
    (w : Fin k → ℝ) : ℝ :=
  ∑ i, Real.sqrt (w i)

/-- The normalization constant `C_{1/2}(w) = A_{1/2}(w)^2 - 1`. -/
noncomputable def pom_diagonal_rate_critical_line_laplacian_first_order_C {k : ℕ}
    (w : Fin k → ℝ) : ℝ :=
  pom_diagonal_rate_critical_line_laplacian_first_order_A w ^ 2 - 1

/-- The kernel vector `√w`. -/
noncomputable def pom_diagonal_rate_critical_line_laplacian_first_order_sqrtVec {k : ℕ}
    (w : Fin k → ℝ) :
    Fin k → ℝ :=
  fun i => Real.sqrt (w i)

/-- The critical-line Laplacian with diagonal `((A / √w_i) - 1) / C` and off-diagonal
`-1 / C`. -/
noncomputable def pom_diagonal_rate_critical_line_laplacian_first_order_Lw {k : ℕ}
    (w : Fin k → ℝ) :
    Fin k → Fin k → ℝ :=
  fun i j =>
    if i = j then
      ((pom_diagonal_rate_critical_line_laplacian_first_order_A w / Real.sqrt (w i)) - 1) /
        pom_diagonal_rate_critical_line_laplacian_first_order_C w
    else
      -1 / pom_diagonal_rate_critical_line_laplacian_first_order_C w

/-- The action of `L_w` on a vector. -/
noncomputable def pom_diagonal_rate_critical_line_laplacian_first_order_act {k : ℕ}
    (w v : Fin k → ℝ) :
    Fin k → ℝ :=
  fun i => ∑ j, pom_diagonal_rate_critical_line_laplacian_first_order_Lw w i j * v j

/-- The first-order perturbation model `I - δ L_w`. -/
noncomputable def pom_diagonal_rate_critical_line_laplacian_first_order_firstOrderAct {k : ℕ}
    (δ : ℝ) (w v : Fin k → ℝ) : Fin k → ℝ :=
  fun i => v i - δ * pom_diagonal_rate_critical_line_laplacian_first_order_act w v i

/-- Paper label: `thm:pom-diagonal-rate-critical-line-laplacian-first-order`.

For a strictly positive probability vector `w` on `Fin k`, the critical-line Laplacian `L_w`
has the advertised entrywise form, is symmetric, has kernel vector `√w`, has nonnegative
quadratic form, and the first-order model `I - δ L_w` sends each eigenvector of `L_w`
with eigenvalue `μ` to the exact first-order eigenvalue `1 - δ μ`. -/
theorem paper_pom_diagonal_rate_critical_line_laplacian_first_order
    (k : ℕ) (hk : 2 ≤ k) (w : Fin k → ℝ)
    (hw_pos : ∀ i, 0 < w i) (hw_sum : (∑ i, w i) = 1)
    (hC_pos : 0 < pom_diagonal_rate_critical_line_laplacian_first_order_C w) :
    (∀ i j,
        pom_diagonal_rate_critical_line_laplacian_first_order_Lw w i j =
          if i = j then
            ((pom_diagonal_rate_critical_line_laplacian_first_order_A w / Real.sqrt (w i)) - 1) /
              pom_diagonal_rate_critical_line_laplacian_first_order_C w
          else
            -1 / pom_diagonal_rate_critical_line_laplacian_first_order_C w) ∧
    (∀ i j,
        pom_diagonal_rate_critical_line_laplacian_first_order_Lw w i j =
          pom_diagonal_rate_critical_line_laplacian_first_order_Lw w j i) ∧
    (∀ v : Fin k → ℝ,
        ∑ i, v i * pom_diagonal_rate_critical_line_laplacian_first_order_act w v i =
          ((∑ i,
                (pom_diagonal_rate_critical_line_laplacian_first_order_A w / Real.sqrt (w i)) *
                  v i ^ 2) -
              (∑ i, v i) ^ 2) /
            pom_diagonal_rate_critical_line_laplacian_first_order_C w) ∧
    (∀ v : Fin k → ℝ,
        0 ≤ ∑ i, v i * pom_diagonal_rate_critical_line_laplacian_first_order_act w v i) ∧
    (∀ i,
        pom_diagonal_rate_critical_line_laplacian_first_order_act w
            (pom_diagonal_rate_critical_line_laplacian_first_order_sqrtVec w) i =
          0) ∧
    (∀ δ μ (v : Fin k → ℝ),
        (∀ i, pom_diagonal_rate_critical_line_laplacian_first_order_act w v i = μ * v i) →
          ∀ i,
            pom_diagonal_rate_critical_line_laplacian_first_order_firstOrderAct δ w v i =
              (1 - δ * μ) * v i) := by
  classical
  let A := pom_diagonal_rate_critical_line_laplacian_first_order_A w
  let C := pom_diagonal_rate_critical_line_laplacian_first_order_C w
  let s := pom_diagonal_rate_critical_line_laplacian_first_order_sqrtVec w
  have hC_ne : C ≠ 0 := ne_of_gt hC_pos
  have hs_pos : ∀ i, 0 < s i := by
    intro i
    dsimp [s, pom_diagonal_rate_critical_line_laplacian_first_order_sqrtVec]
    exact Real.sqrt_pos.2 (hw_pos i)
  have hs_ne : ∀ i, s i ≠ 0 := fun i => ne_of_gt (hs_pos i)
  have hi0 : Fin k := ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hk⟩
  have hA_pos : 0 < A := by
    dsimp [A, pom_diagonal_rate_critical_line_laplacian_first_order_A]
    have hle :
        Real.sqrt (w hi0) ≤ ∑ i, Real.sqrt (w i) := by
      exact Finset.single_le_sum (fun i _ => le_of_lt (Real.sqrt_pos.2 (hw_pos i)))
        (by simp)
    exact lt_of_lt_of_le (Real.sqrt_pos.2 (hw_pos hi0)) hle
  have hA_ne : A ≠ 0 := ne_of_gt hA_pos
  have hs_sum : ∑ i, s i = A := by
    simp [A, s, pom_diagonal_rate_critical_line_laplacian_first_order_A,
      pom_diagonal_rate_critical_line_laplacian_first_order_sqrtVec]
  have hs_sq : ∀ i, s i ^ 2 = w i := by
    intro i
    dsimp [s, pom_diagonal_rate_critical_line_laplacian_first_order_sqrtVec]
    nlinarith [Real.sq_sqrt (le_of_lt (hw_pos i))]
  have hs_mul_inv : ∀ i, A / Real.sqrt (w i) = A / s i := by
    intro i
    simp [s, pom_diagonal_rate_critical_line_laplacian_first_order_sqrtVec]
  have hact_formula :
      ∀ (v : Fin k → ℝ) (i : Fin k),
        pom_diagonal_rate_critical_line_laplacian_first_order_act w v i =
          ((A / s i) * v i - ∑ j, v j) / C := by
    intro v i
    have hsplit :
        ∑ j, (if i = j then ((A / s i) - 1) / C else -1 / C) * v j =
          (((A / s i) - 1) / C) * v i +
            Finset.sum (Finset.univ.erase i) (fun j => (-1 / C) * v j) := by
      calc
        ∑ j, (if i = j then ((A / s i) - 1) / C else -1 / C) * v j
            = (if i = i then ((A / s i) - 1) / C else -1 / C) * v i +
                Finset.sum (Finset.univ.erase i)
                  (fun j => (if i = j then ((A / s i) - 1) / C else -1 / C) * v j) := by
                simpa [add_comm] using
                  (Finset.sum_erase_add (s := (Finset.univ : Finset (Fin k))) (a := i)
                    (f := fun j => (if i = j then ((A / s i) - 1) / C else -1 / C) * v j)
                    (by simp))
        _ = (((A / s i) - 1) / C) * v i +
              Finset.sum (Finset.univ.erase i) (fun j => (-1 / C) * v j) := by
              congr 1
              · simp
              · refine Finset.sum_congr rfl ?_
                intro j hj
                have hji : j ≠ i := (Finset.mem_erase.mp hj).1
                have hij : i ≠ j := by simpa [eq_comm] using hji
                simp [hij]
    calc
      pom_diagonal_rate_critical_line_laplacian_first_order_act w v i
          = ∑ j,
              (if i = j then ((A / s i) - 1) / C else -1 / C) * v j := by
              simpa [pom_diagonal_rate_critical_line_laplacian_first_order_act,
                pom_diagonal_rate_critical_line_laplacian_first_order_Lw, A, C, s, hs_mul_inv i]
      _ = (((A / s i) - 1) / C) * v i +
            Finset.sum (Finset.univ.erase i) (fun j => (-1 / C) * v j) := hsplit
      _ = (((A / s i) - 1) * v i) / C +
            (Finset.sum (Finset.univ.erase i) (fun j => (-1) * v j)) / C := by
            have hsumC :
                Finset.sum (Finset.univ.erase i) (fun j => (-1 / C) * v j) =
                  (Finset.sum (Finset.univ.erase i) (fun j => (-1) * v j)) / C := by
              rw [Finset.sum_div]
              refine Finset.sum_congr rfl ?_
              intro j hj
              ring
            rw [hsumC]
            ring
      _ = ((((A / s i) - 1) * v i) +
            Finset.sum (Finset.univ.erase i) (fun j => (-1) * v j)) / C := by
            field_simp [hC_ne]
      _ = ((((A / s i) - 1) * v i) -
            Finset.sum (Finset.univ.erase i) v) / C := by
            congr 1
            have hneg :
                Finset.sum (Finset.univ.erase i) (fun j => (-1 : ℝ) * v j) =
                  -Finset.sum (Finset.univ.erase i) v := by
              rw [← Finset.mul_sum]
              simp
            rw [hneg]
            ring
      _ = ((A / s i) * v i - ∑ j, v j) / C := by
            have hsum_erase :
                ∑ j, v j = v i + Finset.sum (Finset.univ.erase i) v := by
              simpa [add_comm] using
                (Finset.sum_erase_add (s := (Finset.univ : Finset (Fin k))) (a := i) (f := v)
                  (by simp))
            rw [hsum_erase]
            field_simp [hC_ne]
            ring
  have hquadratic :
      ∀ v : Fin k → ℝ,
        ∑ i, v i * pom_diagonal_rate_critical_line_laplacian_first_order_act w v i =
          ((∑ i, (A / s i) * v i ^ 2) - (∑ i, v i) ^ 2) / C := by
    intro v
    have hsum :
        ∑ i, v i * pom_diagonal_rate_critical_line_laplacian_first_order_act w v i =
          ∑ i, v i * (((A / s i) * v i - ∑ j, v j) / C) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [hact_formula v i]
    rw [hsum]
    have hsumv :
        ∑ i, v i * (((A / s i) * v i - ∑ j, v j) / C) =
          ((∑ i, (A / s i) * v i ^ 2) - (∑ i, v i) * (∑ i, v i)) / C := by
      calc
        ∑ i, v i * (((A / s i) * v i - ∑ j, v j) / C)
            = ∑ i, (v i * ((A / s i) * v i - ∑ j, v j)) / C := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                ring
        _ = (∑ i, v i * ((A / s i) * v i - ∑ j, v j)) / C := by
              rw [Finset.sum_div]
        _ = (∑ i, ((A / s i) * v i ^ 2 - v i * (∑ j, v j))) / C := by
              congr 1
              refine Finset.sum_congr rfl ?_
              intro i hi
              ring
        _ = ((∑ i, (A / s i) * v i ^ 2) - ∑ i, v i * (∑ j, v j)) / C := by
              congr 1
              rw [Finset.sum_sub_distrib]
        _ = ((∑ i, (A / s i) * v i ^ 2) - (∑ i, v i) * (∑ i, v i)) / C := by
              congr 1
              rw [Finset.sum_mul]
    simpa [pow_two] using hsumv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    simp [pom_diagonal_rate_critical_line_laplacian_first_order_Lw]
  · intro i j
    by_cases hij : i = j
    · simp [pom_diagonal_rate_critical_line_laplacian_first_order_Lw, hij]
    · have hji : j ≠ i := by
          intro h
          exact hij h.symm
      simp [pom_diagonal_rate_critical_line_laplacian_first_order_Lw, hij, hji]
  · intro v
    simpa [A, C, s, sq, hs_mul_inv] using hquadratic v
  · intro v
    have hq := hquadratic v
    let β : ℝ := (∑ j, v j) / A
    have hsq_expand :
        ((∑ i, (A / s i) * v i ^ 2) - (∑ i, v i) ^ 2) / C =
          (∑ i, (A / s i) * (v i - β * s i) ^ 2) / C := by
      have hsum1 :
          ∑ i, (A / s i) * (v i - β * s i) ^ 2 =
            ∑ i, (A / s i) * v i ^ 2 - 2 * β * A * (∑ i, v i) + β ^ 2 * A * (∑ i, s i) := by
        calc
          ∑ i, (A / s i) * (v i - β * s i) ^ 2
              = ∑ i, ((A / s i) * v i ^ 2 - 2 * β * A * v i + β ^ 2 * A * s i) := by
                  refine Finset.sum_congr rfl ?_
                  intro i hi
                  have hsqi : s i ^ 2 = w i := hs_sq i
                  have hsni : s i ≠ 0 := hs_ne i
                  field_simp [hsni]
                  ring_nf
          _ = ∑ i, (A / s i) * v i ^ 2 - ∑ i, (2 * β * A * v i) + ∑ i, (β ^ 2 * A * s i) := by
                rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
          _ = ∑ i, (A / s i) * v i ^ 2 - 2 * β * A * (∑ i, v i) + β ^ 2 * A * (∑ i, s i) := by
                rw [← Finset.mul_sum, ← Finset.mul_sum]
      rw [hsum1, hs_sum]
      have hbeta : β * A = ∑ j, v j := by
        dsimp [β]
        field_simp [hA_ne]
      have hbeta_sq : β ^ 2 * A ^ 2 = (∑ j, v j) ^ 2 := by
        dsimp [β]
        field_simp [hA_ne]
      field_simp [hC_ne]
      rw [pow_two]
      nlinarith [hbeta, hbeta_sq]
    rw [hq, hsq_expand]
    have hsum_nonneg :
        0 ≤ ∑ i, (A / s i) * (v i - β * s i) ^ 2 := by
      refine Finset.sum_nonneg ?_
      intro i hi
      have hcoeff : 0 ≤ A / s i := by
        exact le_of_lt (div_pos hA_pos (hs_pos i))
      positivity
    have : 0 ≤ (∑ i, (A / s i) * (v i - β * s i) ^ 2) / C := by
      exact div_nonneg hsum_nonneg (le_of_lt hC_pos)
    simpa [hsq_expand] using this
  · intro i
    have hkern := hact_formula s i
    rw [hkern]
    have hs_sum_sq : ∑ j, s j ^ 2 = 1 := by
      calc
        ∑ j, s j ^ 2 = ∑ j, w j := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          exact hs_sq j
        _ = 1 := hw_sum
    have hAi :
        (A / s i) * s i = A := by
      field_simp [hs_ne i]
    have hs_sum' : ∑ j, s j = A := hs_sum
    have : ((A / s i) * s i - ∑ j, s j) / C = 0 := by
      rw [hAi, hs_sum']
      field_simp [hC_ne]
      ring
    simpa [s] using this
  · intro δ μ v hv i
    dsimp [pom_diagonal_rate_critical_line_laplacian_first_order_firstOrderAct]
    rw [hv i]
    ring

end Omega.POM
