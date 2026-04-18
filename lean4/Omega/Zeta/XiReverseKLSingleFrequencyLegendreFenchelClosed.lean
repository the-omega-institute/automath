import Mathlib

namespace Omega.Zeta

private noncomputable def xiReverseKLObjective (alpha t c : ℝ) : ℝ :=
  t * c + Real.log (1 - alpha * c ^ 2)

private lemma xiReverseKLObjective_mem_image (alpha t c : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    xiReverseKLObjective alpha t c ∈
      (fun c : ℝ => t * c + Real.log (1 - alpha * c ^ 2)) '' Set.Icc (0 : ℝ) 1 := by
  exact ⟨c, hc, rfl⟩

set_option maxHeartbeats 400000 in
theorem paper_xi_reversekl_single_frequency_legendre_fenchel_closed (alpha t : ℝ)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1) (ht : 0 ≤ t) :
    sSup ((fun c : ℝ => t * c + Real.log (1 - alpha * c ^ 2)) '' Set.Icc (0 : ℝ) 1) =
      if t ≤ 2 * alpha / (1 - alpha) then
        let u : ℝ := Real.sqrt (1 + t ^ 2 / alpha)
        u - 1 + Real.log (2 / (u + 1))
      else
        t + Real.log (1 - alpha) := by
  let S : Set ℝ := (fun c : ℝ => t * c + Real.log (1 - alpha * c ^ 2)) '' Set.Icc (0 : ℝ) 1
  have hS_nonempty : S.Nonempty := by
    refine ⟨xiReverseKLObjective alpha t 0, ?_⟩
    exact xiReverseKLObjective_mem_image alpha t 0 ⟨le_rfl, zero_le_one⟩
  have halpha_ne : alpha ≠ 0 := ne_of_gt halpha0
  have hOneSubAlpha : 0 < 1 - alpha := by linarith
  by_cases hbranch : t ≤ 2 * alpha / (1 - alpha)
  · simp [hbranch]
    let u : ℝ := Real.sqrt (1 + t ^ 2 / alpha)
    have hu_nonneg : 0 ≤ u := by
      exact Real.sqrt_nonneg _
    have harg_nonneg : 0 ≤ 1 + t ^ 2 / alpha := by positivity
    have hu_sq : u ^ 2 = 1 + t ^ 2 / alpha := by
      dsimp [u]
      simpa using Real.sq_sqrt harg_nonneg
    have hu_ge_one : 1 ≤ u := by
      have hfrac_nonneg : 0 ≤ t ^ 2 / alpha := by positivity
      nlinarith [hu_sq, hu_nonneg, hfrac_nonneg]
    have hden_pos : 0 < u + 1 := by linarith
    have hdiv_pos : 0 < 2 / (u + 1) := by positivity
    have hupper :
        ∀ y ∈ S, y ≤ u - 1 + Real.log (2 / (u + 1)) := by
      intro y hy
      rcases hy with ⟨c, hc, rfl⟩
      have hc0 : 0 ≤ c := hc.1
      have hc1 : c ≤ 1 := hc.2
      have hc_sq_le : c ^ 2 ≤ 1 := by nlinarith
      have hlog_arg_pos : 0 < 1 - alpha * c ^ 2 := by
        nlinarith [halpha0, halpha1, hc_sq_le]
      let z : ℝ := ((u + 1) * (1 - alpha * c ^ 2)) / 2
      have hz_pos : 0 < z := by
        dsimp [z]
        positivity
      have hz_mul : z * (2 / (u + 1)) = 1 - alpha * c ^ 2 := by
        dsimp [z]
        field_simp [hden_pos.ne']
      have hlog_le : Real.log z ≤ z - 1 := Real.log_le_sub_one_of_pos hz_pos
      have hsquare :
          t * c + z ≤ u := by
        have hsq_nonneg : 0 ≤ (alpha * (u + 1) * c - t) ^ 2 := sq_nonneg _
        have hu_rel : t ^ 2 = alpha * (u - 1) * (u + 1) := by
          have hu_sq' : alpha * u ^ 2 = alpha + t ^ 2 := by
            rw [hu_sq]
            field_simp [halpha_ne]
          nlinarith
        have hquad : 0 ≤ alpha * (u + 1) * c ^ 2 - 2 * t * c + (u - 1) := by
          have hquad_eq :
              alpha * (u + 1) * c ^ 2 - 2 * t * c + (u - 1) =
                (alpha * (u + 1) * c - t) ^ 2 / (alpha * (u + 1)) := by
            field_simp [halpha_ne, hden_pos.ne']
            ring_nf
            rw [hu_rel]
            ring_nf
          rw [hquad_eq]
          positivity
        dsimp [z]
        nlinarith [hquad]
      calc
        t * c + Real.log (1 - alpha * c ^ 2)
            = t * c + (Real.log z + Real.log (2 / (u + 1))) := by
                rw [← hz_mul, Real.log_mul hz_pos.ne' hdiv_pos.ne']
        _ ≤ t * c + ((z - 1) + Real.log (2 / (u + 1))) := by
              linarith
        _ = t * c + (z - 1 + Real.log (2 / (u + 1))) := by ring
        _ ≤ u - 1 + Real.log (2 / (u + 1)) := by
              linarith
    have hS_bdd :
        BddAbove S := ⟨u - 1 + Real.log (2 / (u + 1)), fun y hy => hupper y hy⟩
    have hlower :
        u - 1 + Real.log (2 / (u + 1)) ≤ sSup S := by
      by_cases ht0 : t = 0
      · have hu_eq : u = 1 := by
          have hu_sq_one : u ^ 2 = 1 := by
            rw [hu_sq, ht0]
            field_simp [halpha_ne]
            ring
          nlinarith [hu_sq_one, hu_nonneg]
        have hzero :
            xiReverseKLObjective alpha t 0 = u - 1 + Real.log (2 / (u + 1)) := by
          norm_num [xiReverseKLObjective, ht0, hu_eq]
        rw [← hzero]
        exact le_csSup hS_bdd (xiReverseKLObjective_mem_image alpha t 0 ⟨le_rfl, zero_le_one⟩)
      · have ht_pos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
        let c : ℝ := (u - 1) / t
        have hc_nonneg : 0 ≤ c := by
          dsimp [c]
          exact div_nonneg (sub_nonneg.mpr hu_ge_one) (le_of_lt ht_pos)
        have hu_le : u ≤ t + 1 := by
          have hthr' := hbranch
          field_simp [hOneSubAlpha.ne'] at hthr'
          have hu_sq' : alpha * u ^ 2 = alpha + t ^ 2 := by
            rw [hu_sq]
            field_simp [halpha_ne]
          have hsquare_le : u ^ 2 ≤ (t + 1) ^ 2 := by
            nlinarith [hu_sq', hthr', halpha0]
          nlinarith [hu_nonneg, ht]
        have hc_le : c ≤ 1 := by
          have hsub : u - 1 ≤ t := by linarith [hu_le]
          dsimp [c]
          field_simp [ht0]
          linarith
        have hc : c ∈ Set.Icc (0 : ℝ) 1 := ⟨hc_nonneg, hc_le⟩
        have hu_rel : t ^ 2 = alpha * (u - 1) * (u + 1) := by
          have hu_sq' : alpha * u ^ 2 = alpha + t ^ 2 := by
            rw [hu_sq]
            field_simp [halpha_ne]
          nlinarith
        have hlog_arg :
            1 - alpha * c ^ 2 = 2 / (u + 1) := by
          dsimp [c]
          field_simp [ht0, hden_pos.ne', halpha_ne]
          nlinarith [hu_rel, halpha0]
        have hvalue :
            xiReverseKLObjective alpha t c = u - 1 + Real.log (2 / (u + 1)) := by
          dsimp [xiReverseKLObjective, c]
          have htc : t * ((u - 1) / t) = u - 1 := by
            field_simp [ht0]
          rw [hlog_arg]
          rw [htc]
        rw [← hvalue]
        exact le_csSup hS_bdd (xiReverseKLObjective_mem_image alpha t c hc)
    exact le_antisymm (csSup_le hS_nonempty hupper) hlower
  · simp [hbranch]
    have ht_large : 2 * alpha / (1 - alpha) < t := lt_of_not_ge hbranch
    have hupper :
        ∀ y ∈ S, y ≤ t + Real.log (1 - alpha) := by
      intro y hy
      rcases hy with ⟨c, hc, rfl⟩
      have hc0 : 0 ≤ c := hc.1
      have hc1 : c ≤ 1 := hc.2
      have hc_sq_le : c ^ 2 ≤ 1 := by nlinarith
      have hlog_arg_pos : 0 < 1 - alpha * c ^ 2 := by
        nlinarith [halpha0, halpha1, hc_sq_le]
      let z : ℝ := (1 - alpha * c ^ 2) / (1 - alpha)
      have hz_pos : 0 < z := by
        dsimp [z]
        positivity
      have hz_mul : z * (1 - alpha) = 1 - alpha * c ^ 2 := by
        dsimp [z]
        field_simp [hOneSubAlpha.ne']
      have hlog_le : Real.log z ≤ z - 1 := Real.log_le_sub_one_of_pos hz_pos
      have hz_bound : z - 1 ≤ t * (1 - c) := by
        by_cases hc_eq : c = 1
        · subst hc_eq
          dsimp [z]
          have hz_one : (1 - alpha * 1 ^ 2) / (1 - alpha) = 1 := by
            field_simp [hOneSubAlpha.ne']
          field_simp [hOneSubAlpha.ne']
          linarith [hz_one]
        · have hc_lt : c < 1 := lt_of_le_of_ne hc1 hc_eq
          have h1pc_le : 1 + c ≤ 2 := by linarith
          have haux : alpha * (1 + c) / (1 - alpha) ≤ t := by
            have haux_num : alpha * (1 + c) ≤ 2 * alpha := by
              nlinarith [h1pc_le, halpha0.le]
            have haux' : alpha * (1 + c) / (1 - alpha) ≤ 2 * alpha / (1 - alpha) := by
              field_simp [hOneSubAlpha.ne']
              nlinarith [haux_num, hOneSubAlpha]
            exact haux'.trans ht_large.le
          have hz_formula : z - 1 = alpha * (1 - c) * (1 + c) / (1 - alpha) := by
            dsimp [z]
            field_simp [hOneSubAlpha.ne']
            ring
          have h1c_nonneg : 0 ≤ 1 - c := by linarith
          have hm :
              alpha * (1 - c) * (1 + c) / (1 - alpha) ≤ t * (1 - c) := by
            calc
              alpha * (1 - c) * (1 + c) / (1 - alpha) =
                  (alpha * (1 + c) / (1 - alpha)) * (1 - c) := by
                    field_simp [hOneSubAlpha.ne']
              _ ≤ t * (1 - c) := mul_le_mul_of_nonneg_right haux h1c_nonneg
          simpa [hz_formula] using hm
      calc
        t * c + Real.log (1 - alpha * c ^ 2)
            = t * c + (Real.log z + Real.log (1 - alpha)) := by
                rw [← hz_mul, Real.log_mul hz_pos.ne' hOneSubAlpha.ne']
        _ ≤ t * c + ((z - 1) + Real.log (1 - alpha)) := by
              linarith
        _ = t * c + (z - 1 + Real.log (1 - alpha)) := by ring
        _ ≤ t + Real.log (1 - alpha) := by
              linarith
    have hS_bdd : BddAbove S := ⟨t + Real.log (1 - alpha), fun y hy => hupper y hy⟩
    have hone : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
    have hvalue :
        xiReverseKLObjective alpha t 1 = t + Real.log (1 - alpha) := by
      dsimp [xiReverseKLObjective]
      ring_nf
    have hlower : t + Real.log (1 - alpha) ≤ sSup S := by
      rw [← hvalue]
      exact le_csSup hS_bdd (xiReverseKLObjective_mem_image alpha t 1 hone)
    exact le_antisymm (csSup_le hS_nonempty hupper) hlower

end Omega.Zeta
