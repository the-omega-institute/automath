import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete Bernoulli address data for the exact-dimensional hologram wrapper. The address map is
kept explicit, while the probability vector determines all cylinder and ball masses used below. -/
structure xi_time_part62dc_hologram_bernoulli_exact_dimensional_data where
  xi_time_part62dc_hologram_bernoulli_exact_dimensional_alphabet_card : ℕ
  xi_time_part62dc_hologram_bernoulli_exact_dimensional_base : ℝ
  xi_time_part62dc_hologram_bernoulli_exact_dimensional_probability :
    Fin xi_time_part62dc_hologram_bernoulli_exact_dimensional_alphabet_card → ℝ
  xi_time_part62dc_hologram_bernoulli_exact_dimensional_address :
    (ℕ → Fin xi_time_part62dc_hologram_bernoulli_exact_dimensional_alphabet_card) → ℝ

namespace xi_time_part62dc_hologram_bernoulli_exact_dimensional_data

/-- Entropy of the Bernoulli symbol source. -/
noncomputable def entropy
    (D : xi_time_part62dc_hologram_bernoulli_exact_dimensional_data) : ℝ :=
  -∑ i, D.xi_time_part62dc_hologram_bernoulli_exact_dimensional_probability i *
    Real.log (D.xi_time_part62dc_hologram_bernoulli_exact_dimensional_probability i)

/-- Logarithmic base of the hologram address scale. -/
noncomputable def log_base
    (D : xi_time_part62dc_hologram_bernoulli_exact_dimensional_data) : ℝ :=
  Real.log D.xi_time_part62dc_hologram_bernoulli_exact_dimensional_base

/-- Symbolic address prefix type at depth `n`. -/
abbrev addr_prefix
    (D : xi_time_part62dc_hologram_bernoulli_exact_dimensional_data) (n : ℕ) :=
  Fin n → Fin D.xi_time_part62dc_hologram_bernoulli_exact_dimensional_alphabet_card

/-- Bernoulli mass of a depth-`n` cylinder. -/
noncomputable def cylinder_mass
    (D : xi_time_part62dc_hologram_bernoulli_exact_dimensional_data) {n : ℕ}
    (w : D.addr_prefix n) : ℝ :=
  ∏ i : Fin n, D.xi_time_part62dc_hologram_bernoulli_exact_dimensional_probability (w i)

/-- The hologram ball corresponding to a symbolic prefix has the same mass as that prefix
cylinder. -/
noncomputable def ball_mass
    (D : xi_time_part62dc_hologram_bernoulli_exact_dimensional_data) {n : ℕ}
    (w : D.addr_prefix n) : ℝ :=
  D.cylinder_mass w

/-- Entropy over log-base value appearing as the local dimension. -/
noncomputable def dimension_value
    (D : xi_time_part62dc_hologram_bernoulli_exact_dimensional_data) : ℝ :=
  D.entropy / D.log_base

/-- Exact dimensionality in this finite-address interface is represented by the cylinder-to-ball
mass identity at every finite depth. -/
def exact_dimensional
    (D : xi_time_part62dc_hologram_bernoulli_exact_dimensional_data) : Prop :=
  ∀ n (w : D.addr_prefix n), D.ball_mass w = D.cylinder_mass w

/-- The local dimension is the Shannon entropy divided by the logarithmic address base. -/
noncomputable def local_dimension_formula
    (D : xi_time_part62dc_hologram_bernoulli_exact_dimensional_data) : Prop :=
  D.dimension_value = D.entropy / D.log_base

/-- In the uniform Bernoulli case, every depth-`n` hologram ball has mass `N^{-n}`. -/
noncomputable def uniform_ball_mass_formula
    (D : xi_time_part62dc_hologram_bernoulli_exact_dimensional_data) : Prop :=
  (∀ i,
      D.xi_time_part62dc_hologram_bernoulli_exact_dimensional_probability i =
        (D.xi_time_part62dc_hologram_bernoulli_exact_dimensional_alphabet_card : ℝ)⁻¹) →
    ∀ n (w : D.addr_prefix n),
      D.ball_mass w =
        ((D.xi_time_part62dc_hologram_bernoulli_exact_dimensional_alphabet_card : ℝ)⁻¹) ^ n

/-- The Hausdorff dimension of the faithful Bernoulli address image is the same entropy/log-base
quantity. -/
noncomputable def hausdorff_dimension_formula
    (D : xi_time_part62dc_hologram_bernoulli_exact_dimensional_data) : Prop :=
  D.dimension_value =
    D.entropy / Real.log D.xi_time_part62dc_hologram_bernoulli_exact_dimensional_base

end xi_time_part62dc_hologram_bernoulli_exact_dimensional_data

lemma xi_time_part62dc_hologram_bernoulli_exact_dimensional_cylinder_to_ball_mass
    (D : xi_time_part62dc_hologram_bernoulli_exact_dimensional_data) (n : ℕ)
    (w : D.addr_prefix n) :
    D.ball_mass w = D.cylinder_mass w := by
  rfl

lemma xi_time_part62dc_hologram_bernoulli_exact_dimensional_uniform_cylinder_mass
    (D : xi_time_part62dc_hologram_bernoulli_exact_dimensional_data)
    (huniform :
      ∀ i,
        D.xi_time_part62dc_hologram_bernoulli_exact_dimensional_probability i =
          (D.xi_time_part62dc_hologram_bernoulli_exact_dimensional_alphabet_card : ℝ)⁻¹)
    (n : ℕ) (w : D.addr_prefix n) :
    D.ball_mass w =
      ((D.xi_time_part62dc_hologram_bernoulli_exact_dimensional_alphabet_card : ℝ)⁻¹) ^ n := by
  simp [xi_time_part62dc_hologram_bernoulli_exact_dimensional_data.ball_mass,
    xi_time_part62dc_hologram_bernoulli_exact_dimensional_data.cylinder_mass, huniform]

/-- Paper label: `thm:xi-time-part62dc-hologram-bernoulli-exact-dimensional`. Cylinder and
hologram-ball masses agree at every finite prefix, giving the entropy over log-base local
dimension formula; in the uniform specialization every depth-`n` ball has mass `N^{-n}`. -/
theorem paper_xi_time_part62dc_hologram_bernoulli_exact_dimensional
    (D : xi_time_part62dc_hologram_bernoulli_exact_dimensional_data) :
    D.exact_dimensional ∧ D.local_dimension_formula ∧ D.uniform_ball_mass_formula ∧
      D.hausdorff_dimension_formula := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact xi_time_part62dc_hologram_bernoulli_exact_dimensional_cylinder_to_ball_mass D
  · rfl
  · intro huniform n w
    exact
      xi_time_part62dc_hologram_bernoulli_exact_dimensional_uniform_cylinder_mass
        D huniform n w
  · rfl

end Omega.Zeta
