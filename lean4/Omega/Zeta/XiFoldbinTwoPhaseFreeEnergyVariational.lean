import Omega.Zeta.XiJensenEntropyRegularizedVariational
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

namespace Omega.Zeta

/-- The positive fold-bin phase constant used in the two-phase free-energy package. -/
noncomputable def xi_foldbin_two_phase_free_energy_variational_phi : ℝ :=
  (1 + Real.sqrt 5) / 2

/-- The positive square-root normalization appearing in the prefactor. -/
noncomputable def xi_foldbin_two_phase_free_energy_variational_sqrt5 : ℝ :=
  Real.sqrt 5

/-- The linear field conjugate to the hot phase. -/
noncomputable def xi_foldbin_two_phase_free_energy_variational_L (q : ℝ) : ℝ :=
  (q + 1) * Real.log xi_foldbin_two_phase_free_energy_variational_phi

/-- Binary Shannon entropy on the real interval, with Lean's endpoint convention for `log 0`. -/
noncomputable def xi_foldbin_two_phase_free_energy_variational_binaryEntropy (θ : ℝ) : ℝ :=
  -θ * Real.log θ - (1 - θ) * Real.log (1 - θ)

/-- The two-phase variational functional in Gibbs-normalized form. -/
noncomputable def xi_foldbin_two_phase_free_energy_variational_F (q θ : ℝ) : ℝ :=
  (1 - θ) * Real.log (1 / (1 - θ)) +
    θ * Real.log
      (Real.exp (-xi_foldbin_two_phase_free_energy_variational_L q) / θ)

/-- The unique two-atom optimizer. -/
noncomputable def xi_foldbin_two_phase_free_energy_variational_theta (q : ℝ) : ℝ :=
  Real.exp (-xi_foldbin_two_phase_free_energy_variational_L q) /
    (1 + Real.exp (-xi_foldbin_two_phase_free_energy_variational_L q))

/-- The closed free-energy branch. -/
noncomputable def xi_foldbin_two_phase_free_energy_variational_Psi (q : ℝ) : ℝ :=
  Real.log
      (xi_foldbin_two_phase_free_energy_variational_phi /
        xi_foldbin_two_phase_free_energy_variational_sqrt5) +
    Real.log (1 + Real.exp (-xi_foldbin_two_phase_free_energy_variational_L q))

/-- Paper-facing finite real-calculus package for
`thm:xi-foldbin-two-phase-free-energy-variational`. -/
def xi_foldbin_two_phase_free_energy_variational_statement : Prop :=
  0 < xi_foldbin_two_phase_free_energy_variational_phi ∧
    0 < xi_foldbin_two_phase_free_energy_variational_sqrt5 ∧
    ∀ q : ℝ,
      0 < xi_foldbin_two_phase_free_energy_variational_theta q ∧
        xi_foldbin_two_phase_free_energy_variational_theta q < 1 ∧
        xi_foldbin_two_phase_free_energy_variational_theta q =
          1 / (1 + Real.exp (xi_foldbin_two_phase_free_energy_variational_L q)) ∧
        (∀ θ : ℝ, 0 < θ → θ < 1 →
          xi_foldbin_two_phase_free_energy_variational_F q θ =
            xi_foldbin_two_phase_free_energy_variational_binaryEntropy θ -
              θ * xi_foldbin_two_phase_free_energy_variational_L q) ∧
        (∀ θ : ℝ, 0 < θ → θ < 1 →
          xi_foldbin_two_phase_free_energy_variational_F q θ ≤
            xi_foldbin_two_phase_free_energy_variational_F q
              (xi_foldbin_two_phase_free_energy_variational_theta q)) ∧
        (∀ θ : ℝ, 0 < θ → θ < 1 →
          xi_foldbin_two_phase_free_energy_variational_F q θ =
              xi_foldbin_two_phase_free_energy_variational_F q
                (xi_foldbin_two_phase_free_energy_variational_theta q) →
            θ = xi_foldbin_two_phase_free_energy_variational_theta q) ∧
        Real.log
              (xi_foldbin_two_phase_free_energy_variational_phi /
                xi_foldbin_two_phase_free_energy_variational_sqrt5) +
            xi_foldbin_two_phase_free_energy_variational_F q
              (xi_foldbin_two_phase_free_energy_variational_theta q) =
          xi_foldbin_two_phase_free_energy_variational_Psi q ∧
        HasDerivAt xi_foldbin_two_phase_free_energy_variational_Psi
          (-xi_foldbin_two_phase_free_energy_variational_theta q *
            Real.log xi_foldbin_two_phase_free_energy_variational_phi) q

/-- Paper label: `thm:xi-foldbin-two-phase-free-energy-variational`. -/
theorem paper_xi_foldbin_two_phase_free_energy_variational :
    xi_foldbin_two_phase_free_energy_variational_statement := by
  have hphi : 0 < xi_foldbin_two_phase_free_energy_variational_phi := by
    unfold xi_foldbin_two_phase_free_energy_variational_phi
    positivity
  have hsqrt5 : 0 < xi_foldbin_two_phase_free_energy_variational_sqrt5 := by
    unfold xi_foldbin_two_phase_free_energy_variational_sqrt5
    positivity
  refine ⟨hphi, hsqrt5, ?_⟩
  intro q
  set L : ℝ := xi_foldbin_two_phase_free_energy_variational_L q
  set E : ℝ := Real.exp (-L)
  have hE : 0 < E := by
    dsimp [E]
    positivity
  have hden : 0 < 1 + E := by positivity
  have htheta_pos : 0 < xi_foldbin_two_phase_free_energy_variational_theta q := by
    unfold xi_foldbin_two_phase_free_energy_variational_theta
    exact div_pos hE hden
  have htheta_lt : xi_foldbin_two_phase_free_energy_variational_theta q < 1 := by
    unfold xi_foldbin_two_phase_free_energy_variational_theta
    rw [div_lt_one hden]
    linarith
  have htheta_alt :
      xi_foldbin_two_phase_free_energy_variational_theta q =
        1 / (1 + Real.exp (xi_foldbin_two_phase_free_energy_variational_L q)) := by
    unfold xi_foldbin_two_phase_free_energy_variational_theta
    rw [show xi_foldbin_two_phase_free_energy_variational_L q = L by rfl]
    dsimp [E] at hE
    field_simp [Real.exp_ne_zero L]
    rw [Real.exp_neg]
    field_simp [Real.exp_ne_zero L]
    ring
  have htheta_eq_p0_base :
      1 - xi_foldbin_two_phase_free_energy_variational_theta q = 1 / (1 + E) := by
    unfold xi_foldbin_two_phase_free_energy_variational_theta
    field_simp [hden.ne']
    ring
  have hFtheta :
      xi_foldbin_two_phase_free_energy_variational_F q
          (xi_foldbin_two_phase_free_energy_variational_theta q) =
        Real.log (1 + E) := by
    have hE_ne : E ≠ 0 := hE.ne'
    have hden_ne : 1 + E ≠ 0 := hden.ne'
    unfold xi_foldbin_two_phase_free_energy_variational_F
      xi_foldbin_two_phase_free_energy_variational_theta
    change (1 - E / (1 + E)) * Real.log (1 / (1 - E / (1 + E))) +
        (E / (1 + E)) * Real.log (E / (E / (1 + E))) = Real.log (1 + E)
    have htheta_eq_p0_E : 1 - E / (1 + E) = 1 / (1 + E) := by
      field_simp [hden_ne]
      ring
    rw [htheta_eq_p0_E]
    have hleft : 1 / (1 / (1 + E)) = 1 + E := by
      field_simp [hden_ne]
    have hright : E / (E / (1 + E)) = 1 + E := by
      field_simp [hE_ne, hden_ne]
    rw [hleft, hright]
    rw [← add_mul]
    have hcoeff : 1 / (1 + E) + E / (1 + E) = 1 := by
      field_simp [hden_ne]
    rw [hcoeff]
    ring
  have hF_entropy :
      ∀ θ : ℝ, 0 < θ → θ < 1 →
        xi_foldbin_two_phase_free_energy_variational_F q θ =
          xi_foldbin_two_phase_free_energy_variational_binaryEntropy θ -
            θ * xi_foldbin_two_phase_free_energy_variational_L q := by
    intro θ hθ0 hθ1
    have hθ_ne : θ ≠ 0 := hθ0.ne'
    have h1θ_pos : 0 < 1 - θ := sub_pos.mpr hθ1
    have h1θ_ne : 1 - θ ≠ 0 := h1θ_pos.ne'
    unfold xi_foldbin_two_phase_free_energy_variational_F
      xi_foldbin_two_phase_free_energy_variational_binaryEntropy
    rw [Real.log_div one_ne_zero h1θ_ne, Real.log_one]
    rw [Real.log_div (Real.exp_ne_zero _) hθ_ne, Real.log_exp]
    ring
  have hupper :
      ∀ θ : ℝ, 0 < θ → θ < 1 →
        xi_foldbin_two_phase_free_energy_variational_F q θ ≤
          xi_foldbin_two_phase_free_energy_variational_F q
            (xi_foldbin_two_phase_free_energy_variational_theta q) := by
    intro θ hθ0 hθ1
    have h1θ_pos : 0 < 1 - θ := sub_pos.mpr hθ1
    have hsum : 1 - θ + θ = 1 := by ring
    have hvar := paper_xi_jensen_entropy_regularized_variational
      (w0 := (1 : ℝ)) (w1 := E) (q0 := 1 - θ) (q1 := θ)
      (by norm_num) hE h1θ_pos hθ0 hsum
    calc
      xi_foldbin_two_phase_free_energy_variational_F q θ
          ≤ Real.log (1 + E) := by
            simpa [xi_foldbin_two_phase_free_energy_variational_F, L, E] using hvar.1
      _ = xi_foldbin_two_phase_free_energy_variational_F q
            (xi_foldbin_two_phase_free_energy_variational_theta q) := by
            exact hFtheta.symm
  have hunique :
      ∀ θ : ℝ, 0 < θ → θ < 1 →
        xi_foldbin_two_phase_free_energy_variational_F q θ =
            xi_foldbin_two_phase_free_energy_variational_F q
              (xi_foldbin_two_phase_free_energy_variational_theta q) →
          θ = xi_foldbin_two_phase_free_energy_variational_theta q := by
    intro θ hθ0 hθ1 heq
    have h1θ_pos : 0 < 1 - θ := sub_pos.mpr hθ1
    have hsum : 1 - θ + θ = 1 := by ring
    have hvar := paper_xi_jensen_entropy_regularized_variational
      (w0 := (1 : ℝ)) (w1 := E) (q0 := 1 - θ) (q1 := θ)
      (by norm_num) hE h1θ_pos hθ0 hsum
    have hmax :
        xi_foldbin_two_phase_free_energy_variational_F q θ = Real.log (1 + E) := by
      calc
        xi_foldbin_two_phase_free_energy_variational_F q θ
            = xi_foldbin_two_phase_free_energy_variational_F q
                (xi_foldbin_two_phase_free_energy_variational_theta q) := heq
        _ = Real.log (1 + E) := hFtheta
    have hobj :
        (1 - θ) * Real.log (1 / (1 - θ)) + θ * Real.log (E / θ) =
          Real.log (1 + E) := by
      simpa [xi_foldbin_two_phase_free_energy_variational_F, L, E] using hmax
    exact (hvar.2.2 hobj).2
  have hclosed :
      Real.log
            (xi_foldbin_two_phase_free_energy_variational_phi /
              xi_foldbin_two_phase_free_energy_variational_sqrt5) +
          xi_foldbin_two_phase_free_energy_variational_F q
            (xi_foldbin_two_phase_free_energy_variational_theta q) =
        xi_foldbin_two_phase_free_energy_variational_Psi q := by
    rw [hFtheta]
    rfl
  have hderiv :
      HasDerivAt xi_foldbin_two_phase_free_energy_variational_Psi
        (-xi_foldbin_two_phase_free_energy_variational_theta q *
          Real.log xi_foldbin_two_phase_free_energy_variational_phi) q := by
    set c : ℝ := Real.log xi_foldbin_two_phase_free_energy_variational_phi
    have hL_deriv :
        HasDerivAt xi_foldbin_two_phase_free_energy_variational_L c q := by
      unfold xi_foldbin_two_phase_free_energy_variational_L
      simpa [c, mul_comm] using ((hasDerivAt_id q).add_const (1 : ℝ)).const_mul c
    have hexp :
        HasDerivAt
          (fun x : ℝ => Real.exp (-xi_foldbin_two_phase_free_energy_variational_L x))
          (Real.exp (-xi_foldbin_two_phase_free_energy_variational_L q) * (-c)) q := by
      simpa [c, mul_comm] using hL_deriv.neg.exp
    have hs_ne :
        1 + Real.exp (-xi_foldbin_two_phase_free_energy_variational_L q) ≠ 0 := by
      positivity
    have hlog :
        HasDerivAt
          (fun x : ℝ =>
            Real.log (1 + Real.exp (-xi_foldbin_two_phase_free_energy_variational_L x)))
          ((Real.exp (-xi_foldbin_two_phase_free_energy_variational_L q) * (-c)) /
            (1 + Real.exp (-xi_foldbin_two_phase_free_energy_variational_L q))) q := by
      simpa using (hexp.const_add 1).log hs_ne
    have hconst :
        HasDerivAt
          (fun _ : ℝ =>
            Real.log
              (xi_foldbin_two_phase_free_energy_variational_phi /
                xi_foldbin_two_phase_free_energy_variational_sqrt5)) 0 q :=
      hasDerivAt_const q _
    have htotal := hconst.add hlog
    convert htotal using 1
    · unfold xi_foldbin_two_phase_free_energy_variational_theta
      ring
  exact ⟨htheta_pos, htheta_lt, htheta_alt, hF_entropy, hupper, hunique, hclosed, hderiv⟩

end Omega.Zeta
