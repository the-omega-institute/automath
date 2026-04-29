import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- Concrete data for the main-scale quantile recursion. The interval is represented by the
specified self-map data on real coordinates; `M_injective` and `slope_lower` encode the strictly
monotone main scale and the lower derivative bound used to pull estimates back from `M`-space. -/
structure xi_mainscale_contraction_quantile_recursion_data where
  M : ℝ → ℝ
  E : ℝ → ℝ
  E_tilde : ℝ → ℝ
  T : ℝ → ℝ
  T_tilde : ℝ → ℝ
  n : ℝ
  L : ℝ
  L_tilde : ℝ
  eta : ℝ
  m : ℝ
  fixed : ℝ
  fixed_tilde : ℝ
  L_nonneg : 0 ≤ L
  L_lt_one : L < 1
  L_tilde_lt_one : L_tilde < 1
  m_pos : 0 < m
  M_injective : Function.Injective M
  inverse_eq : ∀ t : ℝ, M (T t) = n - E t
  inverse_tilde_eq : ∀ t : ℝ, M (T_tilde t) = n - E_tilde t
  E_lipschitz : ∀ t u : ℝ, |E t - E u| ≤ L * |M t - M u|
  E_tilde_lipschitz : ∀ t u : ℝ, |E_tilde t - E_tilde u| ≤ L_tilde * |M t - M u|
  perturbation : ∀ t : ℝ, |E t - E_tilde t| ≤ eta
  fixed_eq : T fixed = fixed
  fixed_tilde_eq : T_tilde fixed_tilde = fixed_tilde
  slope_lower : ∀ t u : ℝ, m * |t - u| ≤ |M t - M u|

/-- Pullback distance induced by the main scale. -/
def xi_mainscale_contraction_quantile_recursion_dM
    (D : xi_mainscale_contraction_quantile_recursion_data) (t u : ℝ) : ℝ :=
  |D.M t - D.M u|

/-- The recursion operator is contractive in the pulled-back main-scale metric. -/
def xi_mainscale_contraction_quantile_recursion_isContraction
    (D : xi_mainscale_contraction_quantile_recursion_data) : Prop :=
  ∀ t u : ℝ,
    xi_mainscale_contraction_quantile_recursion_dM D (D.T t) (D.T u) ≤
      D.L * xi_mainscale_contraction_quantile_recursion_dM D t u

/-- Paper-facing conclusion: contraction, unique fixed point with the standard iterated
`L^k` estimate, and the perturbation bounds in `M`-space and in the original coordinate. -/
def xi_mainscale_contraction_quantile_recursion_conclusion
    (D : xi_mainscale_contraction_quantile_recursion_data) : Prop :=
  xi_mainscale_contraction_quantile_recursion_isContraction D ∧
    D.T D.fixed = D.fixed ∧
    (∀ t : ℝ, D.T t = t → t = D.fixed) ∧
    (∀ (k : ℕ) (t : ℝ),
      xi_mainscale_contraction_quantile_recursion_dM D ((D.T^[k]) t) D.fixed ≤
        D.L ^ k * xi_mainscale_contraction_quantile_recursion_dM D t D.fixed) ∧
    |D.M D.fixed_tilde - D.M D.fixed| ≤ D.eta / (1 - D.L_tilde) ∧
    |D.fixed_tilde - D.fixed| ≤ D.eta / ((1 - D.L_tilde) * D.m)

lemma xi_mainscale_contraction_quantile_recursion_bound_of_affine_contraction
    {x eta L : ℝ} (h : x ≤ eta + L * x) (hL : L < 1) :
    x ≤ eta / (1 - L) := by
  have hpos : 0 < 1 - L := by linarith
  apply (le_div_iff₀ hpos).2
  nlinarith

/-- Paper label: `thm:xi-mainscale-contraction-quantile-recursion`. -/
theorem paper_xi_mainscale_contraction_quantile_recursion
    (D : xi_mainscale_contraction_quantile_recursion_data) :
    xi_mainscale_contraction_quantile_recursion_conclusion D := by
  have hcontract : xi_mainscale_contraction_quantile_recursion_isContraction D := by
    intro t u
    unfold xi_mainscale_contraction_quantile_recursion_dM
    rw [D.inverse_eq t, D.inverse_eq u]
    have hrewrite : D.n - D.E t - (D.n - D.E u) = -(D.E t - D.E u) := by ring
    rw [hrewrite, abs_neg]
    exact D.E_lipschitz t u
  have hiterate :
      ∀ (k : ℕ) (t : ℝ),
        xi_mainscale_contraction_quantile_recursion_dM D ((D.T^[k]) t) D.fixed ≤
          D.L ^ k * xi_mainscale_contraction_quantile_recursion_dM D t D.fixed := by
    intro k
    induction k with
    | zero =>
        intro t
        simp
    | succ k ih =>
        intro t
        calc
          xi_mainscale_contraction_quantile_recursion_dM D ((D.T^[k + 1]) t) D.fixed
              = xi_mainscale_contraction_quantile_recursion_dM D
                  (D.T ((D.T^[k]) t)) (D.T D.fixed) := by
                simp [Function.iterate_succ_apply', D.fixed_eq]
          _ ≤ D.L * xi_mainscale_contraction_quantile_recursion_dM D
                  ((D.T^[k]) t) D.fixed := hcontract ((D.T^[k]) t) D.fixed
          _ ≤ D.L * (D.L ^ k *
                  xi_mainscale_contraction_quantile_recursion_dM D t D.fixed) := by
                exact mul_le_mul_of_nonneg_left (ih t) D.L_nonneg
          _ = D.L ^ (k + 1) *
                  xi_mainscale_contraction_quantile_recursion_dM D t D.fixed := by
                ring
  have hunique : ∀ t : ℝ, D.T t = t → t = D.fixed := by
    intro t ht
    have hdist :
        xi_mainscale_contraction_quantile_recursion_dM D t D.fixed ≤
          D.L * xi_mainscale_contraction_quantile_recursion_dM D t D.fixed := by
      simpa [ht, D.fixed_eq] using hcontract t D.fixed
    have hzero :
        xi_mainscale_contraction_quantile_recursion_dM D t D.fixed = 0 := by
      have hnonneg : 0 ≤ xi_mainscale_contraction_quantile_recursion_dM D t D.fixed := by
        unfold xi_mainscale_contraction_quantile_recursion_dM
        positivity
      have hmul :
          xi_mainscale_contraction_quantile_recursion_dM D t D.fixed * (1 - D.L) ≤ 0 := by
        nlinarith
      have hpos : 0 < 1 - D.L := sub_pos.mpr D.L_lt_one
      have hle : xi_mainscale_contraction_quantile_recursion_dM D t D.fixed ≤ 0 := by
        by_contra hnot
        have hdist_pos : 0 < xi_mainscale_contraction_quantile_recursion_dM D t D.fixed :=
          lt_of_not_ge hnot
        have hprod_pos :
            0 < xi_mainscale_contraction_quantile_recursion_dM D t D.fixed * (1 - D.L) :=
          mul_pos hdist_pos hpos
        nlinarith
      exact le_antisymm hle hnonneg
    apply D.M_injective
    unfold xi_mainscale_contraction_quantile_recursion_dM at hzero
    exact sub_eq_zero.mp (abs_eq_zero.mp hzero)
  have hMperturb :
      |D.M D.fixed_tilde - D.M D.fixed| ≤ D.eta / (1 - D.L_tilde) := by
    have hraw :
        |D.M D.fixed_tilde - D.M D.fixed| ≤
          D.eta + D.L_tilde * |D.M D.fixed_tilde - D.M D.fixed| := by
      have hfixed :
          D.M D.fixed_tilde - D.M D.fixed =
            D.E D.fixed - D.E_tilde D.fixed_tilde := by
        calc
          D.M D.fixed_tilde - D.M D.fixed
              = D.M (D.T_tilde D.fixed_tilde) - D.M (D.T D.fixed) := by
                simp [D.fixed_tilde_eq, D.fixed_eq]
          _ = (D.n - D.E_tilde D.fixed_tilde) - (D.n - D.E D.fixed) := by
                rw [D.inverse_tilde_eq, D.inverse_eq]
          _ = D.E D.fixed - D.E_tilde D.fixed_tilde := by ring
      calc
        |D.M D.fixed_tilde - D.M D.fixed|
            = |D.E D.fixed - D.E_tilde D.fixed_tilde| := by rw [hfixed]
        _ = |(D.E D.fixed - D.E_tilde D.fixed) +
              (D.E_tilde D.fixed - D.E_tilde D.fixed_tilde)| := by ring_nf
        _ ≤ |D.E D.fixed - D.E_tilde D.fixed| +
              |D.E_tilde D.fixed - D.E_tilde D.fixed_tilde| := abs_add_le _ _
        _ ≤ D.eta + D.L_tilde * |D.M D.fixed - D.M D.fixed_tilde| := by
              exact add_le_add (D.perturbation D.fixed)
                (D.E_tilde_lipschitz D.fixed D.fixed_tilde)
        _ = D.eta + D.L_tilde * |D.M D.fixed_tilde - D.M D.fixed| := by
              rw [abs_sub_comm]
    exact xi_mainscale_contraction_quantile_recursion_bound_of_affine_contraction
      hraw D.L_tilde_lt_one
  have htperturb :
      |D.fixed_tilde - D.fixed| ≤ D.eta / ((1 - D.L_tilde) * D.m) := by
    have hposL : 0 < 1 - D.L_tilde := sub_pos.mpr D.L_tilde_lt_one
    have hposDen : 0 < (1 - D.L_tilde) * D.m := mul_pos hposL D.m_pos
    have hslope :
        D.m * |D.fixed_tilde - D.fixed| ≤ |D.M D.fixed_tilde - D.M D.fixed| :=
      D.slope_lower D.fixed_tilde D.fixed
    have hscaled :
        D.m * |D.fixed_tilde - D.fixed| ≤ D.eta / (1 - D.L_tilde) :=
      le_trans hslope hMperturb
    apply (le_div_iff₀ hposDen).2
    have hm_nonneg : 0 ≤ D.m := le_of_lt D.m_pos
    have hmain : |D.fixed_tilde - D.fixed| * ((1 - D.L_tilde) * D.m) ≤ D.eta := by
      have hmul := (le_div_iff₀ hposL).1 hscaled
      nlinarith
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmain
  exact ⟨hcontract, D.fixed_eq, hunique, hiterate, hMperturb, htperturb⟩

end

end Omega.Zeta
