import Mathlib.Tactic
import Omega.TypedAddressBiaxialCompletion.CertificateLoop
import Omega.Zeta.ToeplitzPsdCofinalSparsificationHereditary

namespace Omega.Zeta

open Omega.TypedAddressBiaxialCompletion

/-- The robust lower bound propagated from the cofinal audited truncations. -/
noncomputable def xi_toeplitz_psd_robust_cofinal_audit_margin (C : CompiledToeplitzPsdCertificate)
    (r : ℝ) : ℝ :=
  compiledToeplitzSchurDelta C r / 2

/-- A concrete cofinal-audit formulation: a compiled PSD certificate gives a positive margin on
the audited subsequence, hereditary interlacing propagates that margin to all smaller minors, and
therefore every principal minor has strictly positive lower edge. -/
def xi_toeplitz_psd_robust_cofinal_audit_statement : Prop :=
  ∀ (N : ℕ → ℕ) (lambdaMin : ℕ → ℝ) (C : CompiledToeplitzPsdCertificate) (r : ℝ),
    0 ≤ r →
      r < 1 →
      (∀ m, ∃ j, m ≤ N j) →
      (∀ {m n : ℕ}, m ≤ n →
        xi_toeplitz_psd_robust_cofinal_audit_margin C r ≤ lambdaMin n →
          xi_toeplitz_psd_robust_cofinal_audit_margin C r ≤ lambdaMin m) →
      (∀ j, xi_toeplitz_psd_robust_cofinal_audit_margin C r ≤ lambdaMin (N j)) →
      compiledToeplitzTrueBlockPsd C ∧
        (∀ m, xi_toeplitz_psd_robust_cofinal_audit_margin C r ≤ lambdaMin m) ∧
        ∀ m, 0 < lambdaMin m

theorem xi_toeplitz_psd_robust_cofinal_audit_verified :
    xi_toeplitz_psd_robust_cofinal_audit_statement := by
  intro N lambdaMin C r hr0 hr1 hcofinal hhered hcofinalMargin
  have hCertificate :=
    paper_typed_address_biaxial_completion_compiled_psd_certificate C hr0 hr1
  have hPsd : compiledToeplitzTrueBlockPsd C := hCertificate.1
  have hDelta : 0 < compiledToeplitzSchurDelta C r := hCertificate.2.2.1
  let Phi : ℕ → Prop := fun n =>
    xi_toeplitz_psd_robust_cofinal_audit_margin C r ≤ lambdaMin n
  have hAllPhi : ∀ m, Phi m := by
    have hIff :=
      paper_xi_toeplitz_psd_cofinal_sparsification_hereditary Phi
        (fun {_m _n} hmn hPhi => hhered hmn hPhi) N hcofinal
    exact hIff.2 hcofinalMargin
  refine ⟨hPsd, hAllPhi, ?_⟩
  intro m
  have hMarginPos : 0 < xi_toeplitz_psd_robust_cofinal_audit_margin C r := by
    unfold xi_toeplitz_psd_robust_cofinal_audit_margin
    linarith
  exact lt_of_lt_of_le hMarginPos (hAllPhi m)

/-- Paper label: `thm:xi-toeplitz-psd-robust-cofinal-audit`. -/
theorem paper_xi_toeplitz_psd_robust_cofinal_audit :
    xi_toeplitz_psd_robust_cofinal_audit_statement :=
  xi_toeplitz_psd_robust_cofinal_audit_verified

end Omega.Zeta
