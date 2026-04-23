import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.Folding.BinGaugeVolume
import Omega.Folding.FiberEntropySaturation
import Omega.Folding.FoldBinChi2Col
import Omega.Zeta.XiFoldbinGaugeEntropyOneNatLaw

open scoped BigOperators

namespace Omega.Zeta

/-- The normalized bin-fold mass `p_m^{bin}(w) = d_m(w) / 2^m`. -/
noncomputable def xi_foldbin_gauge_escort_kl_decomposition_mass (m : ℕ) (x : Omega.X m) : ℝ :=
  (Omega.X.fiberMultiplicity x : ℝ) / (2 : ℝ) ^ m

/-- The Shannon entropy term `H(p) = -∑ p log p` for the normalized fiber-mass law. -/
noncomputable def xi_foldbin_gauge_escort_kl_decomposition_entropy (m : ℕ) : ℝ :=
  -(∑ x : Omega.X m,
      xi_foldbin_gauge_escort_kl_decomposition_mass m x *
        Real.log (xi_foldbin_gauge_escort_kl_decomposition_mass m x))

/-- The normalized collision mass `Col_m = ∑ p_m(w)^2`. -/
noncomputable def xi_foldbin_gauge_escort_kl_decomposition_collision (m : ℕ) : ℝ :=
  ∑ x : Omega.X m, (xi_foldbin_gauge_escort_kl_decomposition_mass m x) ^ 2

/-- The gauge-density `κ_m = ∑ p_m(w) log d_m(w)`. -/
noncomputable def xi_foldbin_gauge_escort_kl_decomposition_kappa (m : ℕ) : ℝ :=
  ∑ x : Omega.X m,
    xi_foldbin_gauge_escort_kl_decomposition_mass m x * Real.log (Omega.X.fiberMultiplicity x)

/-- The escort-square KL correction rewritten in closed form. -/
noncomputable def xi_foldbin_gauge_escort_kl_decomposition_escort_kl (m : ℕ) : ℝ :=
  Real.log (xi_foldbin_gauge_escort_kl_decomposition_collision m) +
    xi_foldbin_gauge_escort_kl_decomposition_entropy m

/-- Paper label: `thm:xi-foldbin-gauge-escort-kl-decomposition`.
For the normalized fiber-mass law, `κ_m` is `m log 2 - H(p)`, hence also
`log (2^m Col_m) - D_esc`; Jensen gives the upper collision bound, with equality exactly when the
fiber multiplicities are constant, and the existing `χ²` theorem rewrites the same collision term.
-/
theorem paper_xi_foldbin_gauge_escort_kl_decomposition (m : ℕ) :
    xi_foldbin_gauge_escort_kl_decomposition_kappa m =
      (m : ℝ) * Real.log 2 - xi_foldbin_gauge_escort_kl_decomposition_entropy m ∧
    xi_foldbin_gauge_escort_kl_decomposition_kappa m =
      Real.log
          ((2 : ℝ) ^ m * xi_foldbin_gauge_escort_kl_decomposition_collision m) -
        xi_foldbin_gauge_escort_kl_decomposition_escort_kl m ∧
    xi_foldbin_gauge_escort_kl_decomposition_kappa m ≤
      Real.log ((2 : ℝ) ^ m * xi_foldbin_gauge_escort_kl_decomposition_collision m) ∧
    (xi_foldbin_gauge_escort_kl_decomposition_kappa m =
        Real.log ((2 : ℝ) ^ m * xi_foldbin_gauge_escort_kl_decomposition_collision m) ↔
      ∃ c : ℕ, ∀ x : Omega.X m, Omega.X.fiberMultiplicity x = c) ∧
    (((Omega.Folding.foldBinChi2Col m : ℚ) : ℝ) + 1 =
      (Fintype.card (Omega.X m) : ℝ) * (Omega.Folding.foldBinCollisionMass m : ℚ)) := by
  let p : Omega.X m → ℝ := xi_foldbin_gauge_escort_kl_decomposition_mass m
  let H : ℝ := xi_foldbin_gauge_escort_kl_decomposition_entropy m
  let Col : ℝ := xi_foldbin_gauge_escort_kl_decomposition_collision m
  let κ : ℝ := xi_foldbin_gauge_escort_kl_decomposition_kappa m
  let Dkl : ℝ := xi_foldbin_gauge_escort_kl_decomposition_escort_kl m
  have hpow_pos : 0 < (2 : ℝ) ^ m := by positivity
  have hpow_ne : (2 : ℝ) ^ m ≠ 0 := hpow_pos.ne'
  have hmass_pos : ∀ x : Omega.X m, 0 < p x := by
    intro x
    dsimp [p, xi_foldbin_gauge_escort_kl_decomposition_mass]
    exact div_pos (by exact_mod_cast Omega.X.fiberMultiplicity_pos x) hpow_pos
  have hmass_nonneg : ∀ x : Omega.X m, 0 ≤ p x := by
    intro x
    exact (hmass_pos x).le
  have hmass_sum : ∑ x : Omega.X m, p x = 1 := by
    dsimp [p, xi_foldbin_gauge_escort_kl_decomposition_mass]
    have hsum :
        (∑ x : Omega.X m, (Omega.X.fiberMultiplicity x : ℝ)) = (2 : ℝ) ^ m := by
      exact_mod_cast Omega.X.fiberMultiplicity_sum_eq_pow m
    calc
      ∑ x : Omega.X m, (Omega.X.fiberMultiplicity x : ℝ) / (2 : ℝ) ^ m
          = (∑ x : Omega.X m, (Omega.X.fiberMultiplicity x : ℝ)) / (2 : ℝ) ^ m := by
              rw [Finset.sum_div]
      _ = 1 := by
        rw [hsum]
        field_simp [hpow_ne]
  have hkappa_entropy :
      κ = (m : ℝ) * Real.log 2 - H := by
    dsimp [κ, H, p, xi_foldbin_gauge_escort_kl_decomposition_kappa,
      xi_foldbin_gauge_escort_kl_decomposition_entropy]
    have h :=
      paper_xi_foldbin_gauge_entropy_one_nat_law (m := m)
        (mu := fun x : Omega.X m => (Omega.X.fiberMultiplicity x : ℝ) / (2 : ℝ) ^ m)
        (d := fun x : Omega.X m => (Omega.X.fiberMultiplicity x : ℝ))
        (hmu := by intro x; rfl)
        (hprob := hmass_sum)
        (hpos := by
          intro x
          exact hmass_pos x)
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
  have hcol_pos : 0 < Col := by
    dsimp [Col, p, xi_foldbin_gauge_escort_kl_decomposition_collision]
    have hone :
        0 < (xi_foldbin_gauge_escort_kl_decomposition_mass m (Omega.X.ofNat m 0)) ^ 2 := by
      have hpos := hmass_pos (Omega.X.ofNat m 0)
      nlinarith
    have hle :
        (xi_foldbin_gauge_escort_kl_decomposition_mass m (Omega.X.ofNat m 0)) ^ 2 ≤
          ∑ x : Omega.X m, (xi_foldbin_gauge_escort_kl_decomposition_mass m x) ^ 2 := by
      simpa using
        Finset.single_le_sum
          (fun x _hx => sq_nonneg (xi_foldbin_gauge_escort_kl_decomposition_mass m x))
          (Finset.mem_univ (Omega.X.ofNat m 0))
    linarith
  have hcollision_expand :
      ∑ x : Omega.X m, p x * (Omega.X.fiberMultiplicity x : ℝ) = (2 : ℝ) ^ m * Col := by
    dsimp [p, Col, xi_foldbin_gauge_escort_kl_decomposition_mass,
      xi_foldbin_gauge_escort_kl_decomposition_collision]
    calc
      ∑ x : Omega.X m, ((Omega.X.fiberMultiplicity x : ℝ) / (2 : ℝ) ^ m) *
          (Omega.X.fiberMultiplicity x : ℝ)
          =
            ∑ x : Omega.X m,
              (2 : ℝ) ^ m * (((Omega.X.fiberMultiplicity x : ℝ) / (2 : ℝ) ^ m) ^ 2) := by
                apply Finset.sum_congr rfl
                intro x _hx
                field_simp [hpow_ne]
      _ = (2 : ℝ) ^ m *
            ∑ x : Omega.X m, (((Omega.X.fiberMultiplicity x : ℝ) / (2 : ℝ) ^ m) ^ 2) := by
              rw [Finset.mul_sum]
      _ = (2 : ℝ) ^ m * Col := by rfl
  have hupper_raw :
      κ ≤ Real.log ((2 : ℝ) ^ m * Col) ∧
        (κ = Real.log ((2 : ℝ) ^ m * Col) ↔
          ∃ c : ℕ, ∀ x : Omega.X m, Omega.X.fiberMultiplicity x = c) := by
    have hsat :=
      Omega.Folding.paper_fold_fiber_entropy_saturation
        (pi := p) (d := Omega.X.fiberMultiplicity) hmass_nonneg hmass_sum
        (fun x => Omega.X.fiberMultiplicity_pos x)
    rcases hsat with ⟨hineq, heq⟩
    refine ⟨?_, ?_⟩
    · dsimp [κ, p] at hineq
      rw [hcollision_expand] at hineq
      exact hineq
    · constructor
      · intro hEq
        have hEq' :
            ∑ x : Omega.X m, p x * Real.log (Omega.X.fiberMultiplicity x : ℝ) =
              Real.log (∑ x : Omega.X m, p x * Omega.X.fiberMultiplicity x) := by
          calc
            ∑ x : Omega.X m, p x * Real.log (Omega.X.fiberMultiplicity x : ℝ) = κ := by
              simp [κ, p, xi_foldbin_gauge_escort_kl_decomposition_kappa]
            _ = Real.log ((2 : ℝ) ^ m * Col) := hEq
            _ = Real.log (∑ x : Omega.X m, p x * Omega.X.fiberMultiplicity x) := by
              rw [hcollision_expand]
        rcases heq.mp hEq' with ⟨c, hc⟩
        exact ⟨c, fun x => hc x (by linarith [hmass_pos x])⟩
      · rintro ⟨c, hc⟩
        have hEq' :
            ∑ x : Omega.X m, p x * Real.log (Omega.X.fiberMultiplicity x : ℝ) =
              Real.log (∑ x : Omega.X m, p x * Omega.X.fiberMultiplicity x) := by
          apply heq.mpr
          refine ⟨c, ?_⟩
          intro x hx
          exact hc x
        calc
          κ = ∑ x : Omega.X m, p x * Real.log (Omega.X.fiberMultiplicity x : ℝ) := by
            simp [κ, p, xi_foldbin_gauge_escort_kl_decomposition_kappa]
          _ = Real.log (∑ x : Omega.X m, p x * Omega.X.fiberMultiplicity x) := hEq'
          _ = Real.log ((2 : ℝ) ^ m * Col) := by rw [hcollision_expand]
  have hkappa_collision :
      κ = Real.log ((2 : ℝ) ^ m * Col) - Dkl := by
    have hlog_mul :
        Real.log ((2 : ℝ) ^ m * Col) = (m : ℝ) * Real.log 2 + Real.log Col := by
      rw [Real.log_mul hpow_ne hcol_pos.ne', Real.log_pow]
    dsimp [Dkl, Col, H, xi_foldbin_gauge_escort_kl_decomposition_escort_kl]
    rw [hlog_mul, hkappa_entropy]
    ring
  have hchi :
      (((Omega.Folding.foldBinChi2Col m : ℚ) : ℝ) + 1 =
        (Fintype.card (Omega.X m) : ℝ) * (Omega.Folding.foldBinCollisionMass m : ℚ)) := by
    have hchiQ := Omega.Folding.paper_fold_bin_chi2_col m
    have hchiR :
        ((Omega.Folding.foldBinChi2Col m : ℚ) : ℝ) =
          (Fintype.card (Omega.X m) : ℝ) * (Omega.Folding.foldBinCollisionMass m : ℚ) - 1 := by
      exact_mod_cast hchiQ
    linarith
  exact ⟨hkappa_entropy, hkappa_collision, hupper_raw.1, hupper_raw.2, hchi⟩

end Omega.Zeta
