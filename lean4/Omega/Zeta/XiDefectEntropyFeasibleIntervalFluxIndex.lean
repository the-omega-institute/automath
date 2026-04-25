import Mathlib

namespace Omega.Zeta

open scoped BigOperators

/-- The weighted defect entropy `S_def = ∑ m_j δ_j / (1 + δ_j)`. -/
noncomputable def xi_defect_entropy_feasible_interval_flux_index_entropy {κ : ℕ}
    (mass depth : Fin κ → ℝ) : ℝ :=
  ∑ j, mass j * (depth j / (1 + depth j))

/-- The total defect flux `Φ = ∑ m_j δ_j`. -/
noncomputable def xi_defect_entropy_feasible_interval_flux_index_flux {κ : ℕ}
    (mass depth : Fin κ → ℝ) : ℝ :=
  ∑ j, mass j * depth j

/-- The defect index `κ_ind = ∑ m_j`. -/
noncomputable def xi_defect_entropy_feasible_interval_flux_index_index {κ : ℕ}
    (mass : Fin κ → ℝ) : ℝ :=
  ∑ j, mass j

/-- Paper label: `prop:xi-defect-entropy-feasible-interval-flux-index`.
For a finite family of nonnegative depths with multiplicities at least `1`, the defect entropy lies
in the sharp feasible interval between the extreme concentration lower bound and the harmonic-mean
upper bound, and the latter is equivalent to the reciprocal inequality when `Φ > 0`. -/
theorem paper_xi_defect_entropy_feasible_interval_flux_index {κ : ℕ}
    (mass depth : Fin κ → ℝ) (hmass : ∀ j, 1 ≤ mass j) (hdepth : ∀ j, 0 ≤ depth j)
    (hindex_pos : 0 < xi_defect_entropy_feasible_interval_flux_index_index mass) :
    let Φ := xi_defect_entropy_feasible_interval_flux_index_flux mass depth
    let κind := xi_defect_entropy_feasible_interval_flux_index_index mass
    let S := xi_defect_entropy_feasible_interval_flux_index_entropy mass depth
    Φ / (1 + Φ) ≤ S ∧
      S ≤ κind * Φ / (κind + Φ) ∧
      (0 < Φ → 1 / S ≥ 1 / Φ + 1 / κind) := by
  dsimp
  set Φ : ℝ := xi_defect_entropy_feasible_interval_flux_index_flux mass depth with hΦdef
  set κind : ℝ := xi_defect_entropy_feasible_interval_flux_index_index mass with hκdef
  set S : ℝ := xi_defect_entropy_feasible_interval_flux_index_entropy mass depth with hSdef
  set A : ℝ := ∑ j, mass j / (1 + depth j) with hAdef
  set B : ℝ := ∑ j, mass j * (1 + depth j) with hBdef
  have hmass_nonneg : ∀ j, 0 ≤ mass j := fun j => le_trans zero_le_one (hmass j)
  have hΦ_nonneg : 0 ≤ Φ := by
    rw [hΦdef, xi_defect_entropy_feasible_interval_flux_index_flux]
    exact Finset.sum_nonneg fun j _ => mul_nonneg (hmass_nonneg j) (hdepth j)
  have hκ_nonneg : 0 ≤ κind := le_of_lt hindex_pos
  have hterm :
      ∀ j,
        Real.sqrt (mass j / (1 + depth j)) * Real.sqrt (mass j * (1 + depth j)) = mass j := by
    intro j
    have hm : 0 ≤ mass j := hmass_nonneg j
    have hden_nonneg : 0 ≤ 1 + depth j := by
      nlinarith [hdepth j]
    have hden_pos : 0 < 1 + depth j := by
      nlinarith [hdepth j]
    calc
      Real.sqrt (mass j / (1 + depth j)) * Real.sqrt (mass j * (1 + depth j)) =
          Real.sqrt ((mass j / (1 + depth j)) * (mass j * (1 + depth j))) := by
            rw [← Real.sqrt_mul (div_nonneg hm hden_nonneg)]
      _ = Real.sqrt (mass j ^ 2) := by
            congr 1
            field_simp [hden_pos.ne']
      _ = mass j := by
            simpa [abs_of_nonneg hm] using Real.sqrt_sq_eq_abs (mass j)
  have hcs : κind ≤ Real.sqrt A * Real.sqrt B := by
    have h :=
      Real.sum_sqrt_mul_sqrt_le (s := Finset.univ)
        (f := fun j => mass j / (1 + depth j))
        (g := fun j => mass j * (1 + depth j))
        (fun j => div_nonneg (hmass_nonneg j) (by linarith [hdepth j]))
        (fun j => mul_nonneg (hmass_nonneg j) (by linarith [hdepth j]))
    simpa [hκdef, hAdef, hBdef, hterm] using h
  have hB_eq : B = κind + Φ := by
    rw [hBdef, hκdef, hΦdef]
    calc
      ∑ j, mass j * (1 + depth j) = ∑ j, (mass j + mass j * depth j) := by
        refine Finset.sum_congr rfl ?_
        intro j _
        ring
      _ = (∑ j, mass j) + ∑ j, mass j * depth j := by
        rw [Finset.sum_add_distrib]
  have hA_nonneg : 0 ≤ A := by
    rw [hAdef]
    exact Finset.sum_nonneg fun j _ => div_nonneg (hmass_nonneg j) (by linarith [hdepth j])
  have hB_nonneg : 0 ≤ B := by
    rw [hB_eq]
    linarith
  have hsq : κind ^ 2 ≤ A * B := by
    have hsq' : κind ^ 2 ≤ (Real.sqrt A * Real.sqrt B) ^ 2 := by
      nlinarith [hcs, hκ_nonneg]
    calc
      κind ^ 2 ≤ (Real.sqrt A * Real.sqrt B) ^ 2 := hsq'
      _ = A * B := by
            nlinarith [Real.sq_sqrt hA_nonneg, Real.sq_sqrt hB_nonneg]
  have hκΦ_pos : 0 < κind + Φ := by
    linarith
  have hA_lower : κind ^ 2 / (κind + Φ) ≤ A := by
    refine (div_le_iff₀ hκΦ_pos).2 ?_
    simpa [hB_eq, mul_comm, mul_left_comm, mul_assoc]
      using hsq
  have hS_eq : S = κind - A := by
    rw [hSdef, hκdef, hAdef]
    calc
      ∑ j, mass j * (depth j / (1 + depth j)) = ∑ j, (mass j - mass j / (1 + depth j)) := by
        refine Finset.sum_congr rfl ?_
        intro j _
        have hden : (1 + depth j : ℝ) ≠ 0 := by linarith [hdepth j]
        field_simp [hden]
        ring
      _ = ∑ j, mass j - ∑ j, mass j / (1 + depth j) := by
        rw [Finset.sum_sub_distrib]
  have hlower : Φ / (1 + Φ) ≤ S := by
    have hsum :
        ∑ j, mass j * (depth j / (1 + Φ)) ≤ ∑ j, mass j * (depth j / (1 + depth j)) := by
      refine Finset.sum_le_sum ?_
      intro j _
      have hm : 0 ≤ mass j := hmass_nonneg j
      have hsingle : mass j * depth j ≤ Φ := by
        rw [hΦdef, xi_defect_entropy_feasible_interval_flux_index_flux]
        simpa using
          (Finset.single_le_sum
            (fun i _ => mul_nonneg (hmass_nonneg i) (hdepth i))
            (by simp : j ∈ (Finset.univ : Finset (Fin κ))))
      have hdepth_le_mass : depth j ≤ mass j * depth j := by
        nlinarith [hmass j, hdepth j]
      have hdepth_le_Φ : depth j ≤ Φ := by
        exact le_trans hdepth_le_mass hsingle
      have hfrac :
          depth j / (1 + Φ) ≤ depth j / (1 + depth j) := by
        have hdenΦ_pos : 0 < 1 + Φ := by
          nlinarith
        have hdenj_pos : 0 < 1 + depth j := by
          nlinarith [hdepth j]
        refine (div_le_div_iff₀ hdenΦ_pos hdenj_pos).2 ?_
        nlinarith [hdepth j, hdepth_le_Φ]
      exact mul_le_mul_of_nonneg_left hfrac hm
    have hrewrite : ∑ j, mass j * (depth j / (1 + Φ)) = Φ / (1 + Φ) := by
      rw [hΦdef, xi_defect_entropy_feasible_interval_flux_index_flux]
      calc
        ∑ j, mass j * (depth j / (1 + Φ)) = ∑ j, (mass j * depth j) / (1 + Φ) := by
          refine Finset.sum_congr rfl ?_
          intro j _
          ring
        _ = (∑ j, mass j * depth j) / (1 + Φ) := by
          rw [Finset.sum_div]
        _ = Φ / (1 + Φ) := by
          simpa [hΦdef, xi_defect_entropy_feasible_interval_flux_index_flux]
    calc
      Φ / (1 + Φ) = ∑ j, mass j * (depth j / (1 + Φ)) := hrewrite.symm
      _ ≤ ∑ j, mass j * (depth j / (1 + depth j)) := hsum
      _ = S := by
            simpa [hSdef, xi_defect_entropy_feasible_interval_flux_index_entropy]
  have hupper : S ≤ κind * Φ / (κind + Φ) := by
    rw [hS_eq]
    have haux : κind - A ≤ κind - κind ^ 2 / (κind + Φ) := by
      linarith [hA_lower]
    refine haux.trans_eq ?_
    field_simp [hκΦ_pos.ne']
    ring
  refine ⟨hlower, hupper, ?_⟩
  intro hΦ_pos
  have hlower_pos : 0 < Φ / (1 + Φ) := by positivity
  have hS_pos : 0 < S := lt_of_lt_of_le hlower_pos hlower
  have hrecip : 1 / (κind * Φ / (κind + Φ)) ≤ 1 / S := by
    exact one_div_le_one_div_of_le hS_pos hupper
  have hharm :
      1 / (κind * Φ / (κind + Φ)) = 1 / Φ + 1 / κind := by
    field_simp [hΦ_pos.ne', hindex_pos.ne', hκΦ_pos.ne']
  simpa [hharm] using hrecip

end Omega.Zeta
