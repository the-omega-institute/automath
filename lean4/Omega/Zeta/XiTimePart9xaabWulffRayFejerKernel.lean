import Mathlib.Tactic

namespace Omega.Zeta

/-- The centered interval defect for the first `a` residues in an `M`-point window. -/
def xi_time_part9xaab_wulff_ray_fejer_kernel_centeredValue (M a i : ℕ) : ℚ :=
  (if i < a then (1 : ℚ) else 0) - (a : ℚ) / (M : ℚ)

/-- The same centered defect as a function on `Fin M`. -/
def xi_time_part9xaab_wulff_ray_fejer_kernel_centeredDefect (M a : ℕ) (r : Fin M) : ℚ :=
  xi_time_part9xaab_wulff_ray_fejer_kernel_centeredValue M a r.val

/-- A finite Fourier coefficient against an arbitrary rational character. -/
def xi_time_part9xaab_wulff_ray_fejer_kernel_finiteFourierTransform
    (M a : ℕ) (χ : Fin M → ℚ) : ℚ :=
  ∑ r : Fin M, xi_time_part9xaab_wulff_ray_fejer_kernel_centeredDefect M a r * χ r

/-- The zero Fourier mode of the centered Wulff interval defect. -/
def xi_time_part9xaab_wulff_ray_fejer_kernel_zeroMode (M a : ℕ) : ℚ :=
  xi_time_part9xaab_wulff_ray_fejer_kernel_finiteFourierTransform M a (fun _ => 1)

/-- The physical-side Parseval mass of the centered Wulff interval defect. -/
def xi_time_part9xaab_wulff_ray_fejer_kernel_parsevalMass (M a : ℕ) : ℚ :=
  ∑ r : Fin M, (xi_time_part9xaab_wulff_ray_fejer_kernel_centeredDefect M a r) ^ 2

/-- Concrete Wulff-ray Fejér kernel statement: zero mode vanishes and the Parseval mass is the
two-level interval variance. -/
def xi_time_part9xaab_wulff_ray_fejer_kernel_statement (M a : ℕ) : Prop :=
  xi_time_part9xaab_wulff_ray_fejer_kernel_zeroMode M a = 0 ∧
    xi_time_part9xaab_wulff_ray_fejer_kernel_parsevalMass M a =
      (a : ℚ) * (1 - (a : ℚ) / (M : ℚ))

private lemma xi_time_part9xaab_wulff_ray_fejer_kernel_filter_lt_card
    (M a : ℕ) (ha : a ≤ M) :
    ((Finset.range M).filter fun i => i < a).card = a := by
  have hEq : (Finset.range M).filter (fun i => i < a) = Finset.range a := by
    ext i
    constructor
    · intro hi
      exact Finset.mem_range.mpr ((Finset.mem_filter.mp hi).2)
    · intro hi
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hi) ha),
          Finset.mem_range.mp hi⟩
  rw [hEq]
  simp

private lemma xi_time_part9xaab_wulff_ray_fejer_kernel_filter_not_lt_card
    (M a : ℕ) (ha : a ≤ M) :
    ((Finset.range M).filter fun i => ¬ i < a).card = M - a := by
  have hpart :
      ((Finset.range M).filter fun i => i < a).card +
          ((Finset.range M).filter fun i => ¬ i < a).card =
        M := by
    simpa using
      (Finset.card_filter_add_card_filter_not
        (s := Finset.range M) (p := fun i => i < a))
  rw [xi_time_part9xaab_wulff_ray_fejer_kernel_filter_lt_card M a ha] at hpart
  omega

private lemma xi_time_part9xaab_wulff_ray_fejer_kernel_sum_two_level_range
    (M a : ℕ) (ha : a ≤ M) (u v : ℚ) :
    ∑ i ∈ Finset.range M, (if i < a then u else v) =
      (a : ℚ) * u + ((M - a : ℕ) : ℚ) * v := by
  have hlt :
      ∑ i ∈ Finset.range M, (if i < a then u else 0) = (a : ℚ) * u := by
    calc
      ∑ i ∈ Finset.range M, (if i < a then u else 0)
          = ∑ i ∈ (Finset.range M).filter (fun i => i < a), u := by
            rw [Finset.sum_filter]
      _ = (((Finset.range M).filter fun i => i < a).card : ℚ) * u := by simp
      _ = (a : ℚ) * u := by
            rw [xi_time_part9xaab_wulff_ray_fejer_kernel_filter_lt_card M a ha]
  have hge :
      ∑ i ∈ Finset.range M, (if i < a then 0 else v) = ((M - a : ℕ) : ℚ) * v := by
    calc
      ∑ i ∈ Finset.range M, (if i < a then 0 else v)
          = ∑ i ∈ Finset.range M, (if ¬ i < a then v else 0) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            by_cases hia : i < a <;> simp [hia]
      _ = ∑ i ∈ (Finset.range M).filter (fun i => ¬ i < a), v := by
            rw [Finset.sum_filter]
      _ = (((Finset.range M).filter fun i => ¬ i < a).card : ℚ) * v := by simp
      _ = ((M - a : ℕ) : ℚ) * v := by
            rw [xi_time_part9xaab_wulff_ray_fejer_kernel_filter_not_lt_card M a ha]
  calc
    ∑ i ∈ Finset.range M, (if i < a then u else v)
        = ∑ i ∈ Finset.range M,
            ((if i < a then u else 0) + (if i < a then 0 else v)) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          by_cases hia : i < a <;> simp [hia]
    _ =
        (∑ i ∈ Finset.range M, (if i < a then u else 0)) +
          ∑ i ∈ Finset.range M, (if i < a then 0 else v) := by
          rw [Finset.sum_add_distrib]
    _ = (a : ℚ) * u + ((M - a : ℕ) : ℚ) * v := by rw [hlt, hge]

private lemma xi_time_part9xaab_wulff_ray_fejer_kernel_zero_mode_eq_zero
    (M a : ℕ) (hM : 0 < M) (ha : a ≤ M) :
    xi_time_part9xaab_wulff_ray_fejer_kernel_zeroMode M a = 0 := by
  have hM_ne : (M : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hM)
  unfold xi_time_part9xaab_wulff_ray_fejer_kernel_zeroMode
    xi_time_part9xaab_wulff_ray_fejer_kernel_finiteFourierTransform
    xi_time_part9xaab_wulff_ray_fejer_kernel_centeredDefect
  simp
  change
    (∑ r : Fin M,
        xi_time_part9xaab_wulff_ray_fejer_kernel_centeredValue M a r.val) = 0
  rw [Fin.sum_univ_eq_sum_range
    (f := fun i : ℕ => xi_time_part9xaab_wulff_ray_fejer_kernel_centeredValue M a i)]
  unfold xi_time_part9xaab_wulff_ray_fejer_kernel_centeredValue
  calc
    ∑ i ∈ Finset.range M, ((if i < a then (1 : ℚ) else 0) - (a : ℚ) / (M : ℚ))
        = ∑ i ∈ Finset.range M,
            (if i < a then 1 - (a : ℚ) / (M : ℚ) else -(a : ℚ) / (M : ℚ)) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          by_cases hia : i < a
          · simp [hia, sub_eq_add_neg]
          · simp [hia, sub_eq_add_neg]
            ring
    _ =
          (a : ℚ) * (1 - (a : ℚ) / (M : ℚ)) +
            ((M - a : ℕ) : ℚ) * (-(a : ℚ) / (M : ℚ)) := by
          exact xi_time_part9xaab_wulff_ray_fejer_kernel_sum_two_level_range
            M a ha (1 - (a : ℚ) / (M : ℚ)) (-(a : ℚ) / (M : ℚ))
    _ = 0 := by
          rw [Nat.cast_sub ha]
          field_simp [hM_ne]
          ring

private lemma xi_time_part9xaab_wulff_ray_fejer_kernel_parseval_mass_eq
    (M a : ℕ) (hM : 0 < M) (ha : a ≤ M) :
    xi_time_part9xaab_wulff_ray_fejer_kernel_parsevalMass M a =
      (a : ℚ) * (1 - (a : ℚ) / (M : ℚ)) := by
  have hM_ne : (M : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hM)
  unfold xi_time_part9xaab_wulff_ray_fejer_kernel_parsevalMass
    xi_time_part9xaab_wulff_ray_fejer_kernel_centeredDefect
  change
    (∑ r : Fin M,
        (xi_time_part9xaab_wulff_ray_fejer_kernel_centeredValue M a r.val) ^ 2) =
      (a : ℚ) * (1 - (a : ℚ) / (M : ℚ))
  rw [Fin.sum_univ_eq_sum_range
    (f := fun i : ℕ => (xi_time_part9xaab_wulff_ray_fejer_kernel_centeredValue M a i) ^ 2)]
  unfold xi_time_part9xaab_wulff_ray_fejer_kernel_centeredValue
  calc
    ∑ i ∈ Finset.range M, ((if i < a then (1 : ℚ) else 0) - (a : ℚ) / (M : ℚ)) ^ 2
        =
          (a : ℚ) * (1 - (a : ℚ) / (M : ℚ)) ^ 2 +
            ((M - a : ℕ) : ℚ) * (-(a : ℚ) / (M : ℚ)) ^ 2 := by
          refine Eq.trans ?_ (xi_time_part9xaab_wulff_ray_fejer_kernel_sum_two_level_range
            M a ha ((1 - (a : ℚ) / (M : ℚ)) ^ 2)
              ((-(a : ℚ) / (M : ℚ)) ^ 2))
          refine Finset.sum_congr rfl ?_
          intro i hi
          by_cases hia : i < a
          · simp [hia, sub_eq_add_neg]
          · simp [hia, sub_eq_add_neg]
            ring
    _ = (a : ℚ) * (1 - (a : ℚ) / (M : ℚ)) := by
          rw [Nat.cast_sub ha]
          field_simp [hM_ne]
          ring

/-- Paper label: `thm:xi-time-part9xaab-wulff-ray-fejer-kernel`. -/
theorem paper_xi_time_part9xaab_wulff_ray_fejer_kernel (M a : ℕ) (hM : 0 < M)
    (ha : a ≤ M) : xi_time_part9xaab_wulff_ray_fejer_kernel_statement M a := by
  exact
    ⟨xi_time_part9xaab_wulff_ray_fejer_kernel_zero_mode_eq_zero M a hM ha,
      xi_time_part9xaab_wulff_ray_fejer_kernel_parseval_mass_eq M a hM ha⟩

end Omega.Zeta
