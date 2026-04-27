import Mathlib.Tactic
import Omega.Zeta.TerminalZmTranslationTBranchDiscriminantC3Closed

namespace Omega.Zeta

open Polynomial

noncomputable section

/-- Minimal concrete datum for the `μ₃` covariance and discriminant-weight package. -/
structure xi_terminal_zm_translation_t_branch_discriminant_c3_mu3_weight_data where
  xi_terminal_zm_translation_t_branch_discriminant_c3_mu3_weight_witness : Unit := ()

/-- A concrete branch-form surrogate with the same `μ₃` covariance monomials:
`tu` and `u^3` are fixed by `(t,u) ↦ (ζ²t,ζu)` when `ζ³ = 1`. -/
def xi_terminal_zm_translation_t_branch_discriminant_c3_mu3_weight_branchForm
    {R : Type*} [CommRing R] (t μ u : R) : R :=
  μ ^ 3 + t * u + u ^ 3

/-- The exponent appearing in the discriminant covariance calculation for degree `11`. -/
def xi_terminal_zm_translation_t_branch_discriminant_c3_mu3_weight_exponent : ℕ :=
  4 * 11 - 4 + 2 * 11 * (11 - 1)

/-- The factor `A(s)` in the closed `t^4 Φ(t^3)` discriminant package. -/
def xi_terminal_zm_translation_t_branch_discriminant_c3_mu3_weight_A :
    Polynomial ℤ :=
  80 * X ^ 2 + 16424 * X - 84375

/-- The factor `B(s)` in the closed `t^4 Φ(t^3)` discriminant package. -/
def xi_terminal_zm_translation_t_branch_discriminant_c3_mu3_weight_B :
    Polynomial ℤ :=
  256 * X ^ 2 - 1312 * X + 3125

/-- The factor `C(s)` in the closed `t^4 Φ(t^3)` discriminant package. -/
def xi_terminal_zm_translation_t_branch_discriminant_c3_mu3_weight_C :
    Polynomial ℤ :=
  8000 * X ^ 4 + 429800 * X ^ 3 + 96378087 * X ^ 2 - 2034256 * X - 64

/-- The polynomial `Φ(s)` in `Δ(t) = t^4 Φ(t^3)`. -/
def xi_terminal_zm_translation_t_branch_discriminant_c3_mu3_weight_Phi :
    Polynomial ℤ :=
  (515978035200 : Polynomial ℤ) *
    xi_terminal_zm_translation_t_branch_discriminant_c3_mu3_weight_A *
      xi_terminal_zm_translation_t_branch_discriminant_c3_mu3_weight_B ^ 2 *
        xi_terminal_zm_translation_t_branch_discriminant_c3_mu3_weight_C ^ 3

/-- The closed discriminant polynomial, recorded only through its audited `t^4 Φ(t^3)` shape. -/
def xi_terminal_zm_translation_t_branch_discriminant_c3_mu3_weight_Delta :
    Polynomial ℤ :=
  X ^ 4 * xi_terminal_zm_translation_t_branch_discriminant_c3_mu3_weight_Phi.comp (X ^ 3)

namespace xi_terminal_zm_translation_t_branch_discriminant_c3_mu3_weight_data

/-- Concrete `μ₃` covariance package: the closed discriminant covariance plus the branch-form
covariance under `(t,u) ↦ (ζ²t,ζu)`. -/
def xi_terminal_zm_translation_t_branch_discriminant_c3_mu3_weight_covariance
    (_D : xi_terminal_zm_translation_t_branch_discriminant_c3_mu3_weight_data) : Prop :=
  xi_terminal_zm_translation_t_branch_discriminant_c3_closed_covariant ∧
    ∀ ζ t μ u : ℂ, ζ ^ 3 = 1 →
      xi_terminal_zm_translation_t_branch_discriminant_c3_mu3_weight_branchForm
          (ζ ^ 2 * t) μ (ζ * u) =
        xi_terminal_zm_translation_t_branch_discriminant_c3_mu3_weight_branchForm t μ u

/-- The degree-`11` discriminant covariance exponent has weight `2` modulo `3`. -/
def xi_terminal_zm_translation_t_branch_discriminant_c3_mu3_weight_discriminant_weight
    (_D : xi_terminal_zm_translation_t_branch_discriminant_c3_mu3_weight_data) : Prop :=
  xi_terminal_zm_translation_t_branch_discriminant_c3_mu3_weight_exponent = 260 ∧
    xi_terminal_zm_translation_t_branch_discriminant_c3_mu3_weight_exponent % 3 = 2 ∧
      ∀ ζ : ℂ, ζ ^ 3 = 1 →
        ζ ^ xi_terminal_zm_translation_t_branch_discriminant_c3_mu3_weight_exponent = ζ ^ 2

/-- The closed discriminant has the paper-facing `t^4 Φ(t^3)` shape over `ℤ[t]`. -/
def xi_terminal_zm_translation_t_branch_discriminant_c3_mu3_weight_t4_shape
    (_D : xi_terminal_zm_translation_t_branch_discriminant_c3_mu3_weight_data) : Prop :=
  ∃ Φ : Polynomial ℤ,
    xi_terminal_zm_translation_t_branch_discriminant_c3_mu3_weight_Delta =
      X ^ 4 * Φ.comp (X ^ 3)

end xi_terminal_zm_translation_t_branch_discriminant_c3_mu3_weight_data

/-- Paper label:
`thm:xi-terminal-zm-translation-t-branch-discriminant-c3-mu3-weight`. -/
theorem paper_xi_terminal_zm_translation_t_branch_discriminant_c3_mu3_weight
    (D : xi_terminal_zm_translation_t_branch_discriminant_c3_mu3_weight_data) :
    D.xi_terminal_zm_translation_t_branch_discriminant_c3_mu3_weight_covariance ∧
      D.xi_terminal_zm_translation_t_branch_discriminant_c3_mu3_weight_discriminant_weight ∧
        D.xi_terminal_zm_translation_t_branch_discriminant_c3_mu3_weight_t4_shape := by
  refine ⟨?_, ?_, ?_⟩
  · rcases paper_xi_terminal_zm_translation_t_branch_discriminant_c3_closed with ⟨_, hcov⟩
    refine ⟨hcov, ?_⟩
    intro ζ t μ u hζ
    unfold xi_terminal_zm_translation_t_branch_discriminant_c3_mu3_weight_branchForm
    ring_nf
    simp [hζ]
  · refine ⟨by native_decide, by native_decide, ?_⟩
    intro ζ hζ
    have hζ258 : ζ ^ 258 = 1 := by
      calc
        ζ ^ 258 = ζ ^ (3 * 86) := by norm_num
        _ = (ζ ^ 3) ^ 86 := by rw [pow_mul]
        _ = 1 := by simp [hζ]
    calc
      ζ ^ xi_terminal_zm_translation_t_branch_discriminant_c3_mu3_weight_exponent =
          ζ ^ 260 := by
            rw [xi_terminal_zm_translation_t_branch_discriminant_c3_mu3_weight_exponent]
      _ = ζ ^ (258 + 2) := by norm_num
      _ = ζ ^ 258 * ζ ^ 2 := by rw [pow_add]
      _ = ζ ^ 2 := by simp [hζ258]
  · exact ⟨xi_terminal_zm_translation_t_branch_discriminant_c3_mu3_weight_Phi, rfl⟩

end

end Omega.Zeta
