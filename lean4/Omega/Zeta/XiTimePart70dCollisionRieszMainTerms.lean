import Omega.Zeta.XiTimePart70dCentralFiberSecondMoment

open Filter
open scoped Topology

namespace Omega.Zeta

noncomputable section

/-- Collision probability and nontrivial Fourier-energy data for the terminal sheet. -/
structure xi_time_part70d_collision_riesz_main_terms_data where
  xi_time_part70d_collision_riesz_main_terms_collision : ℕ → ℝ
  xi_time_part70d_collision_riesz_main_terms_fiberCount : ℕ → ℝ
  xi_time_part70d_collision_riesz_main_terms_nontrivialEnergy : ℕ → ℝ
  xi_time_part70d_collision_riesz_main_terms_collision_main :
    Tendsto
      (fun m : ℕ =>
        xi_time_part70d_collision_riesz_main_terms_collision m * Real.goldenRatio ^ m)
      atTop (nhds (2 / Real.sqrt 5))
  xi_time_part70d_collision_riesz_main_terms_fiber_collision_limit :
    Tendsto
      (fun m : ℕ =>
        xi_time_part70d_collision_riesz_main_terms_fiberCount m *
          xi_time_part70d_collision_riesz_main_terms_collision m)
      atTop (nhds (2 * Real.goldenRatio ^ 2 / 5))
  xi_time_part70d_collision_riesz_main_terms_parseval_nontrivial :
    ∀ m : ℕ,
      xi_time_part70d_collision_riesz_main_terms_nontrivialEnergy m =
        xi_time_part70d_collision_riesz_main_terms_fiberCount m *
          xi_time_part70d_collision_riesz_main_terms_collision m - 1

/-- Paper-facing collision and Riesz-energy main terms. -/
def xi_time_part70d_collision_riesz_main_terms_statement
    (D : xi_time_part70d_collision_riesz_main_terms_data) : Prop :=
  Tendsto
      (fun m : ℕ =>
        D.xi_time_part70d_collision_riesz_main_terms_collision m * Real.goldenRatio ^ m)
      atTop (nhds (2 / Real.sqrt 5)) ∧
    Tendsto
      (fun m : ℕ =>
        D.xi_time_part70d_collision_riesz_main_terms_fiberCount m *
          D.xi_time_part70d_collision_riesz_main_terms_collision m)
      atTop (nhds (2 * Real.goldenRatio ^ 2 / 5)) ∧
    Tendsto D.xi_time_part70d_collision_riesz_main_terms_nontrivialEnergy atTop
      (nhds (1 / (5 * Real.goldenRatio ^ 3)))

lemma xi_time_part70d_collision_riesz_main_terms_energy_constant :
    2 * Real.goldenRatio ^ 2 / 5 - 1 = 1 / (5 * Real.goldenRatio ^ 3) := by
  let φ : ℝ := Real.goldenRatio
  have hφpos : 0 < φ := by simpa [φ] using Real.goldenRatio_pos
  have hφsq : φ ^ 2 = φ + 1 := by simp [φ]
  have hφcube : φ ^ 3 = 2 * φ + 1 := by
    calc
      φ ^ 3 = φ * φ ^ 2 := by ring
      _ = φ * (φ + 1) := by rw [hφsq]
      _ = 2 * φ + 1 := by nlinarith
  have hφfive : φ ^ 5 = 5 * φ + 3 := by
    calc
      φ ^ 5 = φ ^ 3 * φ ^ 2 := by ring
      _ = (2 * φ + 1) * (φ + 1) := by rw [hφcube, hφsq]
      _ = 5 * φ + 3 := by nlinarith
  change 2 * φ ^ 2 / 5 - 1 = 1 / (5 * φ ^ 3)
  have hden : 5 * φ ^ 3 ≠ 0 := by positivity
  rw [eq_div_iff hden]
  ring_nf
  nlinarith [hφcube, hφfive]

/-- Paper label: `thm:xi-time-part70d-collision-riesz-main-terms`. -/
theorem paper_xi_time_part70d_collision_riesz_main_terms
    (D : xi_time_part70d_collision_riesz_main_terms_data) :
    xi_time_part70d_collision_riesz_main_terms_statement D := by
  refine
    ⟨D.xi_time_part70d_collision_riesz_main_terms_collision_main,
      D.xi_time_part70d_collision_riesz_main_terms_fiber_collision_limit, ?_⟩
  have henergy :
      Tendsto D.xi_time_part70d_collision_riesz_main_terms_nontrivialEnergy atTop
        (nhds (2 * Real.goldenRatio ^ 2 / 5 - 1)) := by
    have hseq :
        D.xi_time_part70d_collision_riesz_main_terms_nontrivialEnergy =
          fun m : ℕ =>
            D.xi_time_part70d_collision_riesz_main_terms_fiberCount m *
              D.xi_time_part70d_collision_riesz_main_terms_collision m - 1 := by
      funext m
      exact D.xi_time_part70d_collision_riesz_main_terms_parseval_nontrivial m
    have hlim :
        Tendsto
          (fun m : ℕ =>
            D.xi_time_part70d_collision_riesz_main_terms_fiberCount m *
              D.xi_time_part70d_collision_riesz_main_terms_collision m - 1) atTop
          (nhds (2 * Real.goldenRatio ^ 2 / 5 - 1)) :=
      D.xi_time_part70d_collision_riesz_main_terms_fiber_collision_limit.sub
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1))
    simpa [hseq] using hlim
  convert henergy using 1
  simpa [Real.goldenRatio_sq] using
    xi_time_part70d_collision_riesz_main_terms_energy_constant.symm

end

end Omega.Zeta
