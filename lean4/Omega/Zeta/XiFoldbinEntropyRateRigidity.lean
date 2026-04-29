import Omega.Zeta.FoldbinShannonDeficitConstantClosedForm
import Omega.Zeta.XiFoldbinPushforwardUniformTwoAtomLedger

namespace Omega.Zeta

/-- The entropy-rate side of `cor:xi-foldbin-entropy-rate-rigidity`, read directly from the
verified uniform two-atom ledger. -/
def xi_foldbin_entropy_rate_rigidity_entropy_rate_limit : Prop :=
  ∀ q : ℕ,
    let θ := derivedBinfoldLimitLaw q true
    derivedBinfoldLimitLaw q = xiEscortBlockLaw θ ∧
      derivedBinfoldSwappedLaw q = xiEscortBlockLaw (1 - θ) ∧
      xiEscortBlockUniformTvCollapse (fun _ => derivedBinfoldLimitLaw q) θ 0 ∧
      derivedBinfoldTv q =
        (|derivedBinfoldLimitLaw q false - derivedBinfoldSwappedLaw q false| +
            |derivedBinfoldLimitLaw q true - derivedBinfoldSwappedLaw q true|) / 2 ∧
      derivedBinfoldBayesError q = 1 / (1 + Real.goldenRatio ^ (q + 1)) ∧
      ∀ g : Bool → ℝ,
        (∑ b : Bool, derivedBinfoldLimitLaw q b * g b) =
          derivedBinfoldLimitLaw q false * g false +
            derivedBinfoldLimitLaw q true * g true

/-- The constant-deficit and exponential-error side of the rigidity corollary. -/
def xi_foldbin_entropy_rate_rigidity_deficit_constant_exponential_convergence : Prop :=
  (∃ C_KL : ℝ,
    C_KL =
        ((3 * Real.goldenRatio - 1) / Real.sqrt 5) * Real.log Real.goldenRatio -
          (1 / 2 : ℝ) * Real.log 5 ∧
      0 < C_KL) ∧
    ∀ m : ℕ, derivedBinfoldErrorTerm m = xiEscortCollapseRate m

/-- Paper label: `cor:xi-foldbin-entropy-rate-rigidity`. -/
theorem paper_xi_foldbin_entropy_rate_rigidity :
    xi_foldbin_entropy_rate_rigidity_entropy_rate_limit ∧
      xi_foldbin_entropy_rate_rigidity_deficit_constant_exponential_convergence := by
  rcases paper_xi_foldbin_pushforward_uniform_two_atom_ledger with ⟨hTwoAtom, hError⟩
  exact ⟨hTwoAtom, paper_xi_foldbin_shannon_deficit_constant_closed_form, hError⟩

end Omega.Zeta
