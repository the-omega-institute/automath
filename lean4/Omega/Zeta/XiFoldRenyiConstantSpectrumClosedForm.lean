import Omega.Zeta.XiFoldbinAbsoluteRenyiEntropyConstantClosed

namespace Omega.Zeta

noncomputable section

/-- Concrete parameter package for the bin-fold Rényi constant spectrum. -/
structure xi_fold_renyi_constant_spectrum_closed_form_data where
  xi_fold_renyi_constant_spectrum_closed_form_q : ℝ := 2

namespace xi_fold_renyi_constant_spectrum_closed_form_data

/-- The closed constant term for the non-Shannon Rényi orders. -/
def xi_fold_renyi_constant_spectrum_closed_form_renyi_constant
    (D : xi_fold_renyi_constant_spectrum_closed_form_data) : ℝ :=
  (1 / (1 - D.xi_fold_renyi_constant_spectrum_closed_form_q)) *
    Real.log
      ((Real.goldenRatio + Real.goldenRatio ^ (-D.xi_fold_renyi_constant_spectrum_closed_form_q)) /
        Real.sqrt 5)

/-- The continuous Shannon extension at `q = 1`. -/
def xi_fold_renyi_constant_spectrum_closed_form_shannon_constant
    (_D : xi_fold_renyi_constant_spectrum_closed_form_data) : ℝ :=
  xi_foldbin_absolute_renyi_entropy_constant_closed_shannon_constant

/-- Paper-facing `q ≠ 1` closed-form identity. -/
def xi_fold_renyi_constant_spectrum_closed_form_renyi_constant_formula
    (D : xi_fold_renyi_constant_spectrum_closed_form_data) : Prop :=
  D.xi_fold_renyi_constant_spectrum_closed_form_q ≠ 1 →
    D.xi_fold_renyi_constant_spectrum_closed_form_renyi_constant =
      xi_foldbin_absolute_renyi_entropy_constant_closed_renyi_constant
        D.xi_fold_renyi_constant_spectrum_closed_form_q

/-- Paper-facing Shannon endpoint identity, recorded separately from the `q ≠ 1` formula. -/
def xi_fold_renyi_constant_spectrum_closed_form_shannon_extension
    (D : xi_fold_renyi_constant_spectrum_closed_form_data) : Prop :=
  D.xi_fold_renyi_constant_spectrum_closed_form_shannon_constant =
    Real.log Real.goldenRatio / (1 + Real.goldenRatio ^ 2)

end xi_fold_renyi_constant_spectrum_closed_form_data

open xi_fold_renyi_constant_spectrum_closed_form_data

/-- Paper label: `thm:xi-fold-renyi-constant-spectrum-closed-form`. -/
theorem paper_xi_fold_renyi_constant_spectrum_closed_form
    (D : xi_fold_renyi_constant_spectrum_closed_form_data) :
    D.xi_fold_renyi_constant_spectrum_closed_form_renyi_constant_formula ∧
      D.xi_fold_renyi_constant_spectrum_closed_form_shannon_extension := by
  refine ⟨?_, ?_⟩
  · intro _hq
    rfl
  · rfl

end

end Omega.Zeta
