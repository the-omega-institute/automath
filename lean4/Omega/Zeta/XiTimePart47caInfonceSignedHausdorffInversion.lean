import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

private lemma xi_time_part47ca_infonce_signed_hausdorff_inversion_alt_sum
    (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), (-1 : ℝ) ^ j * (Nat.choose n j : ℝ)) =
      if n = 0 then 1 else 0 := by
  exact_mod_cast Int.alternating_sum_range_choose (n := n)

private lemma xi_time_part47ca_infonce_signed_hausdorff_inversion_Icc_shift
    (r q : ℕ) (hrq : r ≤ q) (f : ℕ → ℝ) :
    (∑ K ∈ Finset.Icc r q, f K) =
      ∑ j ∈ Finset.range (q - r + 1), f (r + j) := by
  refine Finset.sum_bij (fun K hK => K - r) ?_ ?_ ?_ ?_
  · intro K hK
    have hKq : K ≤ q := (Finset.mem_Icc.mp hK).2
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (Nat.sub_le_sub_right hKq r)
  · intro a ha b hb hab
    have har : r ≤ a := (Finset.mem_Icc.mp ha).1
    have hbr : r ≤ b := (Finset.mem_Icc.mp hb).1
    change a - r = b - r at hab
    calc
      a = r + (a - r) := (Nat.add_sub_of_le har).symm
      _ = r + (b - r) := by rw [hab]
      _ = b := Nat.add_sub_of_le hbr
  · intro j hj
    have hjle : j ≤ q - r := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    refine ⟨r + j, ?_, ?_⟩
    · rw [Finset.mem_Icc]
      constructor
      · exact Nat.le_add_right r j
      · omega
    · exact Nat.add_sub_cancel_left r j
  · intro K hK
    congr 1
    exact (Nat.add_sub_of_le (Finset.mem_Icc.mp hK).1).symm

private lemma xi_time_part47ca_infonce_signed_hausdorff_inversion_choose_mul
    {q r K : ℕ} (hr : 1 ≤ r) (hrK : r ≤ K) :
    Nat.choose (q - 1) (K - 1) * Nat.choose (K - 1) (r - 1) =
      Nat.choose (q - 1) (r - 1) * Nat.choose (q - r) (K - r) := by
  have hsub₁ : (q - 1) - (r - 1) = q - r := by omega
  have hsub₂ : (K - 1) - (r - 1) = K - r := by omega
  simpa [hsub₁, hsub₂] using
    (Nat.choose_mul (n := q - 1) (k := K - 1) (s := r - 1) (by omega))

private lemma xi_time_part47ca_infonce_signed_hausdorff_inversion_inner
    (q r : ℕ) (hr : 1 ≤ r) (hrq : r ≤ q) :
    (∑ K ∈ Finset.Icc r q,
        (-1 : ℝ) ^ K * (Nat.choose (q - 1) (K - 1) : ℝ) *
          (Nat.choose (K - 1) (r - 1) : ℝ)) =
      if r = q then (-1 : ℝ) ^ q else 0 := by
  rw [xi_time_part47ca_infonce_signed_hausdorff_inversion_Icc_shift r q hrq]
  calc
    (∑ j ∈ Finset.range (q - r + 1),
        (-1 : ℝ) ^ (r + j) * (Nat.choose (q - 1) (r + j - 1) : ℝ) *
          (Nat.choose (r + j - 1) (r - 1) : ℝ)) =
        (Nat.choose (q - 1) (r - 1) : ℝ) * (-1 : ℝ) ^ r *
          ∑ j ∈ Finset.range (q - r + 1), (-1 : ℝ) ^ j * (Nat.choose (q - r) j : ℝ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro j hj
      have hpow : (-1 : ℝ) ^ (r + j) = (-1 : ℝ) ^ r * (-1 : ℝ) ^ j := by
        rw [pow_add]
      have hchoose :
          Nat.choose (q - 1) (r + j - 1) * Nat.choose (r + j - 1) (r - 1) =
            Nat.choose (q - 1) (r - 1) * Nat.choose (q - r) j := by
        have := xi_time_part47ca_infonce_signed_hausdorff_inversion_choose_mul
          (q := q) (r := r) (K := r + j) hr (by omega)
        simpa [Nat.add_sub_cancel_left] using this
      rw [hpow]
      calc
        (-1 : ℝ) ^ r * (-1 : ℝ) ^ j * (Nat.choose (q - 1) (r + j - 1) : ℝ) *
            (Nat.choose (r + j - 1) (r - 1) : ℝ) =
            (-1 : ℝ) ^ r * (-1 : ℝ) ^ j *
              ((Nat.choose (q - 1) (r + j - 1) *
                Nat.choose (r + j - 1) (r - 1) : ℕ) : ℝ) := by
          norm_num
          ring
        _ = (-1 : ℝ) ^ r * (-1 : ℝ) ^ j *
              ((Nat.choose (q - 1) (r - 1) * Nat.choose (q - r) j : ℕ) : ℝ) := by
          rw [hchoose]
        _ = (Nat.choose (q - 1) (r - 1) : ℝ) * (-1 : ℝ) ^ r *
              ((-1 : ℝ) ^ j * (Nat.choose (q - r) j : ℝ)) := by
          norm_num
          ring
    _ = if r = q then (-1 : ℝ) ^ q else 0 := by
      rw [xi_time_part47ca_infonce_signed_hausdorff_inversion_alt_sum (q - r)]
      by_cases h : r = q
      · subst q
        simp
      · have hqr : q - r ≠ 0 := by omega
        simp [h, hqr]

private lemma xi_time_part47ca_infonce_signed_hausdorff_inversion_sum_expand
    (η p L : ℕ → ℝ)
    (htri : ∀ K ≥ 2,
      L K = Finset.sum (Finset.Icc 2 K) (fun q =>
        (-1 : ℝ) ^ q * η q * Nat.choose (K - 1) (q - 1) * p q))
    (q : ℕ) (hq : 2 ≤ q) :
    (∑ K ∈ Finset.Icc 2 q, (-1 : ℝ) ^ K * Nat.choose (q - 1) (K - 1) * L K) =
      η q * p q := by
  calc
    (∑ K ∈ Finset.Icc 2 q, (-1 : ℝ) ^ K *
        Nat.choose (q - 1) (K - 1) * L K) =
        ∑ K ∈ Finset.Icc 2 q, (-1 : ℝ) ^ K *
          Nat.choose (q - 1) (K - 1) *
            (∑ r ∈ Finset.Icc 2 K,
              (-1 : ℝ) ^ r * η r * Nat.choose (K - 1) (r - 1) * p r) := by
      refine Finset.sum_congr rfl ?_
      intro K hK
      rw [htri K (Finset.mem_Icc.mp hK).1]
    _ = ∑ K ∈ Finset.Icc 2 q,
          ∑ r ∈ Finset.Icc 2 K,
            ((-1 : ℝ) ^ K * (Nat.choose (q - 1) (K - 1) : ℝ) *
              ((-1 : ℝ) ^ r * η r * (Nat.choose (K - 1) (r - 1) : ℝ) * p r)) := by
      refine Finset.sum_congr rfl ?_
      intro K hK
      rw [Finset.mul_sum]
    _ = ∑ K ∈ Finset.Icc 2 q,
          ∑ r ∈ (Finset.Icc 2 q).filter (fun r => r ≤ K),
            ((-1 : ℝ) ^ K * (Nat.choose (q - 1) (K - 1) : ℝ) *
              ((-1 : ℝ) ^ r * η r * (Nat.choose (K - 1) (r - 1) : ℝ) * p r)) := by
      refine Finset.sum_congr rfl ?_
      intro K hK
      refine Finset.sum_congr ?_ ?_
      · ext r
        have hKq : K ≤ q := (Finset.mem_Icc.mp hK).2
        simp [Finset.mem_Icc]
        omega
      · intro r hr
        rfl
    _ = ∑ r ∈ Finset.Icc 2 q,
          ∑ K ∈ Finset.Icc 2 q,
            if r ≤ K then
              ((-1 : ℝ) ^ K * (Nat.choose (q - 1) (K - 1) : ℝ) *
                ((-1 : ℝ) ^ r * η r * (Nat.choose (K - 1) (r - 1) : ℝ) * p r))
            else 0 := by
      calc
        (∑ K ∈ Finset.Icc 2 q,
          ∑ r ∈ (Finset.Icc 2 q).filter (fun r => r ≤ K),
            ((-1 : ℝ) ^ K * (Nat.choose (q - 1) (K - 1) : ℝ) *
              ((-1 : ℝ) ^ r * η r * (Nat.choose (K - 1) (r - 1) : ℝ) * p r))) =
            ∑ K ∈ Finset.Icc 2 q,
              ∑ r ∈ Finset.Icc 2 q,
                if r ≤ K then
                  ((-1 : ℝ) ^ K * (Nat.choose (q - 1) (K - 1) : ℝ) *
                    ((-1 : ℝ) ^ r * η r * (Nat.choose (K - 1) (r - 1) : ℝ) * p r))
                else 0 := by
          refine Finset.sum_congr rfl ?_
          intro K hK
          rw [Finset.sum_filter]
        _ = ∑ r ∈ Finset.Icc 2 q,
              ∑ K ∈ Finset.Icc 2 q,
                if r ≤ K then
                  ((-1 : ℝ) ^ K * (Nat.choose (q - 1) (K - 1) : ℝ) *
                    ((-1 : ℝ) ^ r * η r * (Nat.choose (K - 1) (r - 1) : ℝ) * p r))
                else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ r ∈ Finset.Icc 2 q,
          ∑ K ∈ (Finset.Icc 2 q).filter (fun K => r ≤ K),
            ((-1 : ℝ) ^ K * (Nat.choose (q - 1) (K - 1) : ℝ) *
              ((-1 : ℝ) ^ r * η r * (Nat.choose (K - 1) (r - 1) : ℝ) * p r)) := by
      refine Finset.sum_congr rfl ?_
      intro r hr
      rw [Finset.sum_filter]
    _ = ∑ r ∈ Finset.Icc 2 q,
          ((-1 : ℝ) ^ r * η r * p r) *
            (∑ K ∈ Finset.Icc r q,
              (-1 : ℝ) ^ K * (Nat.choose (q - 1) (K - 1) : ℝ) *
                (Nat.choose (K - 1) (r - 1) : ℝ)) := by
      refine Finset.sum_congr rfl ?_
      intro r hr
      rw [Finset.mul_sum]
      refine Finset.sum_congr ?_ ?_
      · ext K
        constructor
        · intro hK
          have hKmem := (Finset.mem_filter.mp hK).1
          have hrK := (Finset.mem_filter.mp hK).2
          exact Finset.mem_Icc.mpr ⟨hrK, (Finset.mem_Icc.mp hKmem).2⟩
        · intro hK
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_Icc.mpr
              ⟨le_trans (Finset.mem_Icc.mp hr).1 (Finset.mem_Icc.mp hK).1,
                (Finset.mem_Icc.mp hK).2⟩,
              (Finset.mem_Icc.mp hK).1⟩
      · intro K hK
        ring
    _ = ∑ r ∈ Finset.Icc 2 q,
          ((-1 : ℝ) ^ r * η r * p r) * (if r = q then (-1 : ℝ) ^ q else 0) := by
      refine Finset.sum_congr rfl ?_
      intro r hr
      rw [xi_time_part47ca_infonce_signed_hausdorff_inversion_inner q r
        (le_trans (by norm_num : 1 ≤ 2) (Finset.mem_Icc.mp hr).1)
        (Finset.mem_Icc.mp hr).2]
    _ = η q * p q := by
      rw [Finset.sum_eq_single q]
      · have hsign : (-1 : ℝ) ^ q * (-1 : ℝ) ^ q = 1 := by
          rw [← mul_pow]
          norm_num
        simp only [if_true]
        calc
          (-1 : ℝ) ^ q * η q * p q * (-1 : ℝ) ^ q =
              ((-1 : ℝ) ^ q * (-1 : ℝ) ^ q) * (η q * p q) := by ring
          _ = η q * p q := by rw [hsign]; ring
      · intro r hr hrq
        simp [hrq]
      · intro hqnot
        exact False.elim (hqnot (Finset.mem_Icc.mpr ⟨hq, le_rfl⟩))

/-- Paper label: `thm:xi-time-part47ca-infonce-signed-hausdorff-inversion`. -/
theorem paper_xi_time_part47ca_infonce_signed_hausdorff_inversion
    (η p L : ℕ → ℝ) (hη : ∀ q ≥ 2, η q ≠ 0)
    (htri : ∀ K ≥ 2,
      L K = Finset.sum (Finset.Icc 2 K) (fun q =>
        (-1 : ℝ) ^ q * η q * Nat.choose (K - 1) (q - 1) * p q)) :
    ∀ q ≥ 2,
      p q =
        (η q)⁻¹ *
          ∑ K ∈ Finset.Icc 2 q, (-1 : ℝ) ^ K * Nat.choose (q - 1) (K - 1) * L K := by
  intro q hq
  have hsum :=
    xi_time_part47ca_infonce_signed_hausdorff_inversion_sum_expand η p L htri q hq
  calc
    p q = (η q)⁻¹ * (η q * p q) := by
      symm
      rw [← mul_assoc, inv_mul_cancel₀ (hη q hq), one_mul]
    _ = (η q)⁻¹ *
        ∑ K ∈ Finset.Icc 2 q, (-1 : ℝ) ^ K * Nat.choose (q - 1) (K - 1) * L K := by
      rw [hsum]

end

end Omega.Zeta
