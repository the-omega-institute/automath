import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-lucas-normalized-stiffness-newton-potential`. -/
theorem paper_conclusion_lucas_normalized_stiffness_newton_potential
    (F : ℕ → ℤ) (v : ℤ → ℤ) (stiff : ℕ → ℤ)
    (hstiff : ∀ q,
      stiff q = 2 * (∑ d ∈ Finset.Icc 1 q, ((q + 1 - d : ℕ) : ℤ) * v (F d))) :
    (∀ q, 1 ≤ q → stiff q =
      2 * (∑ d ∈ Finset.Icc 1 q, ((q + 1 - d : ℕ) : ℤ) * v (F d))) ∧
      (∀ q, 2 ≤ q →
        stiff q - 2 * stiff (q - 1) + stiff (q - 2) = 2 * v (F q)) := by
  constructor
  · intro q _hq
    exact hstiff q
  · intro q hq
    let g : ℕ → ℤ := fun d => v (F d)
    let A : ℕ → ℤ := fun n =>
      ∑ d ∈ Finset.Icc 1 n, ((n + 1 - d : ℕ) : ℤ) * g d
    have hstiff' : ∀ n, stiff n = 2 * A n := by
      intro n
      simpa [A, g] using hstiff n
    have hsplit_q :
        A q = (∑ d ∈ Finset.Icc 1 (q - 1), ((q + 1 - d : ℕ) : ℤ) * g d) +
          g q := by
      have htop :
          ∑ d ∈ Finset.Icc 1 q, ((q + 1 - d : ℕ) : ℤ) * g d =
            (∑ d ∈ Finset.Icc 1 (q - 1), ((q + 1 - d : ℕ) : ℤ) * g d) +
              ((q + 1 - q : ℕ) : ℤ) * g q := by
        simpa [show q - 1 + 1 = q by omega] using
          (Finset.sum_Icc_succ_top
            (a := 1) (b := q - 1) (show 1 ≤ q - 1 + 1 by omega)
            (f := fun d => ((q + 1 - d : ℕ) : ℤ) * g d))
      calc
        A q = ∑ d ∈ Finset.Icc 1 q, ((q + 1 - d : ℕ) : ℤ) * g d := rfl
        _ = (∑ d ∈ Finset.Icc 1 (q - 1), ((q + 1 - d : ℕ) : ℤ) * g d) +
              ((q + 1 - q : ℕ) : ℤ) * g q := htop
        _ = (∑ d ∈ Finset.Icc 1 (q - 1), ((q + 1 - d : ℕ) : ℤ) * g d) +
              g q := by
          have hcoeff : (q + 1 - q : ℕ) = 1 := by omega
          rw [hcoeff]
          norm_num
    have hsplit_qm1 :
        A (q - 1) =
          ∑ d ∈ Finset.Icc 1 (q - 1), ((q - d : ℕ) : ℤ) * g d := by
      refine Finset.sum_congr rfl ?_
      intro d hd
      have hdle : d ≤ q - 1 := (Finset.mem_Icc.mp hd).2
      have hcast : ((q - 1 + 1 - d : ℕ) : ℤ) = ((q - d : ℕ) : ℤ) := by
        congr 1
        omega
      simp [hcast]
    have hsplit_qm2 :
        A (q - 2) =
          ∑ d ∈ Finset.Icc 1 (q - 2), ((q - 1 - d : ℕ) : ℤ) * g d := by
      refine Finset.sum_congr rfl ?_
      intro d hd
      have hdle : d ≤ q - 2 := (Finset.mem_Icc.mp hd).2
      have hcast : ((q - 2 + 1 - d : ℕ) : ℤ) = ((q - 1 - d : ℕ) : ℤ) := by
        congr 1
        omega
      simp [hcast]
    have hsplit_base :
        ∑ d ∈ Finset.Icc 1 (q - 1), ((q + 1 - d : ℕ) : ℤ) * g d =
          ∑ d ∈ Finset.Icc 1 (q - 1), (((q - d : ℕ) : ℤ) + 1) * g d := by
      refine Finset.sum_congr rfl ?_
      intro d hd
      have hdle : d ≤ q - 1 := (Finset.mem_Icc.mp hd).2
      have hstep : (q + 1 - d : ℕ) = (q - d) + 1 := by omega
      rw [hstep]
      norm_num
    have hsplit_base' :
        ∑ d ∈ Finset.Icc 1 (q - 1), ((q - d : ℕ) : ℤ) * g d =
          (∑ d ∈ Finset.Icc 1 (q - 2), ((q - d : ℕ) : ℤ) * g d) +
            g (q - 1) := by
      have htop :
          ∑ d ∈ Finset.Icc 1 (q - 1), ((q - d : ℕ) : ℤ) * g d =
            (∑ d ∈ Finset.Icc 1 (q - 2), ((q - d : ℕ) : ℤ) * g d) +
              ((q - (q - 1) : ℕ) : ℤ) * g (q - 1) := by
        simpa [show q - 2 + 1 = q - 1 by omega] using
          (Finset.sum_Icc_succ_top
            (a := 1) (b := q - 2) (show 1 ≤ q - 2 + 1 by omega)
            (f := fun d => ((q - d : ℕ) : ℤ) * g d))
      calc
        ∑ d ∈ Finset.Icc 1 (q - 1), ((q - d : ℕ) : ℤ) * g d =
            (∑ d ∈ Finset.Icc 1 (q - 2), ((q - d : ℕ) : ℤ) * g d) +
              ((q - (q - 1) : ℕ) : ℤ) * g (q - 1) := htop
        _ = (∑ d ∈ Finset.Icc 1 (q - 2), ((q - d : ℕ) : ℤ) * g d) +
              g (q - 1) := by
          have hcoeff : (q - (q - 1) : ℕ) = 1 := by omega
          rw [hcoeff]
          norm_num
    have hsplit_base'' :
        ∑ d ∈ Finset.Icc 1 (q - 1), (((q - d : ℕ) : ℤ) + 1) * g d =
          (∑ d ∈ Finset.Icc 1 (q - 1), ((q - d : ℕ) : ℤ) * g d) +
            ∑ d ∈ Finset.Icc 1 (q - 1), g d := by
      simp only [add_mul, one_mul, Finset.sum_add_distrib]
    have hfirst :
        A q - A (q - 1) = (∑ d ∈ Finset.Icc 1 (q - 1), g d) + g q := by
      rw [hsplit_q, hsplit_qm1, hsplit_base, hsplit_base'']
      ring
    have hsplit_tail :
        ∑ d ∈ Finset.Icc 1 (q - 1), g d =
          (∑ d ∈ Finset.Icc 1 (q - 2), g d) + g (q - 1) := by
      simpa [show q - 2 + 1 = q - 1 by omega] using
        (Finset.sum_Icc_succ_top
          (a := 1) (b := q - 2) (show 1 ≤ q - 2 + 1 by omega)
          (f := fun d => g d))
    have hsplit_second :
        ∑ d ∈ Finset.Icc 1 (q - 1), ((q - d : ℕ) : ℤ) * g d =
          ∑ d ∈ Finset.Icc 1 (q - 1), (((q - 1 - d : ℕ) : ℤ) + 1) * g d := by
      refine Finset.sum_congr rfl ?_
      intro d hd
      have hdle : d ≤ q - 1 := (Finset.mem_Icc.mp hd).2
      by_cases hlast : d = q - 1
      · subst d
        have hq1 : (q - (q - 1) : ℕ) = 1 := by omega
        have hq0 : (q - 1 - (q - 1) : ℕ) = 0 := by omega
        rw [hq1, hq0]
        norm_num
      · have hdle' : d ≤ q - 2 := by omega
        have hstep : (q - d : ℕ) = (q - 1 - d) + 1 := by omega
        rw [hstep]
        norm_num
    have hsecond :
        A (q - 1) - A (q - 2) = ∑ d ∈ Finset.Icc 1 (q - 1), g d := by
      rw [hsplit_qm1, hsplit_qm2, hsplit_second]
      have hsum_split :
          ∑ d ∈ Finset.Icc 1 (q - 1), (((q - 1 - d : ℕ) : ℤ) + 1) * g d =
            (∑ d ∈ Finset.Icc 1 (q - 1), ((q - 1 - d : ℕ) : ℤ) * g d) +
              ∑ d ∈ Finset.Icc 1 (q - 1), g d := by
        simp only [add_mul, one_mul, Finset.sum_add_distrib]
      rw [hsum_split]
      have hzero_last : ((q - 1 - (q - 1) : ℕ) : ℤ) * g (q - 1) = 0 := by
        have hcoeff : (q - 1 - (q - 1) : ℕ) = 0 := by omega
        rw [hcoeff]
        norm_num
      have hsum_top :
          ∑ d ∈ Finset.Icc 1 (q - 1), ((q - 1 - d : ℕ) : ℤ) * g d =
            ∑ d ∈ Finset.Icc 1 (q - 2), ((q - 1 - d : ℕ) : ℤ) * g d := by
        calc
          ∑ d ∈ Finset.Icc 1 (q - 1), ((q - 1 - d : ℕ) : ℤ) * g d =
              (∑ d ∈ Finset.Icc 1 (q - 2), ((q - 1 - d : ℕ) : ℤ) * g d) +
                ((q - 1 - (q - 1) : ℕ) : ℤ) * g (q - 1) := by
            simpa [show q - 2 + 1 = q - 1 by omega] using
              (Finset.sum_Icc_succ_top
                (a := 1) (b := q - 2)
                (show 1 ≤ q - 2 + 1 by omega)
                (f := fun d => ((q - 1 - d : ℕ) : ℤ) * g d)
                )
          _ = ∑ d ∈ Finset.Icc 1 (q - 2), ((q - 1 - d : ℕ) : ℤ) * g d := by
            rw [hzero_last]
            ring
      rw [hsum_top]
      ring
    rw [hstiff' q, hstiff' (q - 1), hstiff' (q - 2)]
    have hA : A q - 2 * A (q - 1) + A (q - 2) = g q := by
      have hcalc :
          A q - 2 * A (q - 1) + A (q - 2) =
            (A q - A (q - 1)) - (A (q - 1) - A (q - 2)) := by ring
      rw [hcalc, hfirst, hsecond]
      ring
    have hA' : A q - 2 * A (q - 1) + A (q - 2) = v (F q) := by
      simpa [g] using hA
    rw [← hA']
    ring

end Omega.Conclusion
