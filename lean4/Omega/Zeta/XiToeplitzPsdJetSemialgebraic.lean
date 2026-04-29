import Mathlib.Tactic
import Omega.Zeta.XiLocalJetDeterminesFiniteCMVAndToeplitzCertificate
import Omega.Zeta.XiVerblunskyFromLocalJet

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- Concrete finite jet data for the Toeplitz-PSD semialgebraic criterion. The local jet and
Carathéodory coefficients determine a finite Verblunsky prefix, the Toeplitz determinant prefix,
and a positive denominator used to clear the rational dependence. -/
structure xi_toeplitz_psd_jet_semialgebraic_data where
  ell : ℕ → ℝ
  coeff : ℕ → ℝ
  coeff_zero : coeff 0 = -ell 1
  coeff_one : coeff 1 = -ell 2
  coeff_two : coeff 2 = ell 2 - ell 3
  coeff_zero_pos : 0 < coeff 0
  N : ℕ
  delta0 : ℝ
  hdelta0 : 0 < delta0
  clearingDenominator : ℝ
  clearingDenominator_pos : 0 < clearingDenominator

/-- The local jet package fed into the existing Verblunsky-from-jet theorem. -/
def xi_toeplitz_psd_jet_semialgebraic_jet_data
    (D : xi_toeplitz_psd_jet_semialgebraic_data) : XiVerblunskyLocalJetData where
  ell := D.ell
  coeff := D.coeff
  coeff_zero := D.coeff_zero
  coeff_one := D.coeff_one
  coeff_two := D.coeff_two
  coeff_zero_pos := D.coeff_zero_pos

/-- The finite Verblunsky prefix read off from the local jet. -/
def xi_toeplitz_psd_jet_semialgebraic_verblunsky_prefix
    (D : xi_toeplitz_psd_jet_semialgebraic_data) : Fin D.N → ℝ :=
  xiFiniteCMVPrefix D.ell D.N

/-- The Toeplitz determinant package induced by the jet-determined Verblunsky prefix. -/
def xi_toeplitz_psd_jet_semialgebraic_toeplitz_data
    (D : xi_toeplitz_psd_jet_semialgebraic_data) : XiToeplitzDetVerblunskyData :=
  xiToeplitzDetDataFromJet D.ell D.N D.delta0 D.hdelta0

/-- The finite prefix of Toeplitz principal determinants determined by the local jet. -/
def xi_toeplitz_psd_jet_semialgebraic_toeplitz_det_prefix
    (D : xi_toeplitz_psd_jet_semialgebraic_data) : Fin (D.N + 1) → ℝ :=
  xiFiniteToeplitzDetPrefix D.ell D.N D.delta0 D.hdelta0

/-- The polynomially cleared determinant inequality used in the semialgebraic packaging. -/
def xi_toeplitz_psd_jet_semialgebraic_cleared_minor
    (D : xi_toeplitz_psd_jet_semialgebraic_data) (m : Fin (D.N + 1)) : ℝ :=
  D.clearingDenominator ^ (m.1 + 1) *
    xi_toeplitz_psd_jet_semialgebraic_toeplitz_det_prefix D m

/-- The finite Toeplitz-PSD test on the jet-determined determinant prefix. -/
def xi_toeplitz_psd_jet_semialgebraic_toeplitz_psd_criterion
    (D : xi_toeplitz_psd_jet_semialgebraic_data) : Prop :=
  ∀ m : Fin (D.N + 1),
    0 ≤ xi_toeplitz_psd_jet_semialgebraic_toeplitz_det_prefix D m

/-- The cleared semialgebraic version of the same finite Toeplitz-PSD test. -/
def xi_toeplitz_psd_jet_semialgebraic_cleared_psd_criterion
    (D : xi_toeplitz_psd_jet_semialgebraic_data) : Prop :=
  ∀ m : Fin (D.N + 1), 0 ≤ xi_toeplitz_psd_jet_semialgebraic_cleared_minor D m

/-- Paper-facing Toeplitz/jet semialgebraic package: the local jet determines the finite
Verblunsky prefix and determinant prefix, the dependence is finite-prefix/rational, and after
clearing the fixed positive denominator the finite Toeplitz-PSD criterion becomes a finite family
of scalar inequalities. -/
def xi_toeplitz_psd_jet_semialgebraic_statement
    (D : xi_toeplitz_psd_jet_semialgebraic_data) : Prop :=
  let J := xi_toeplitz_psd_jet_semialgebraic_jet_data D
  let T := xi_toeplitz_psd_jet_semialgebraic_toeplitz_data D
  xiVerblunskyFromJet D.ell 0 = D.coeff 1 / D.coeff 0 ∧
    xiVerblunskyFromJet D.ell 1 =
      (D.coeff 0 * D.coeff 2 - D.coeff 1 ^ 2) / (D.coeff 0 ^ 2 - D.coeff 1 ^ 2) ∧
    (∀ n ≤ D.N, XiVerblunskyCoeffDependsOnPrefix J n ∧ XiVerblunskyJetDependsOnPrefix J n) ∧
    (∀ j : Fin D.N,
      xi_toeplitz_psd_jet_semialgebraic_verblunsky_prefix D j = xiVerblunskyFromJet D.ell j) ∧
    (∀ m : Fin (D.N + 1),
      xi_toeplitz_psd_jet_semialgebraic_toeplitz_det_prefix D m =
        D.delta0 * Finset.prod (Finset.range m) T.stepFactor) ∧
    (∀ m : Fin (D.N + 1),
      0 ≤ xi_toeplitz_psd_jet_semialgebraic_cleared_minor D m ↔
        0 ≤ xi_toeplitz_psd_jet_semialgebraic_toeplitz_det_prefix D m) ∧
    (xi_toeplitz_psd_jet_semialgebraic_cleared_psd_criterion D ↔
      xi_toeplitz_psd_jet_semialgebraic_toeplitz_psd_criterion D)

/-- Clearing a positive denominator does not change the sign of a finite Toeplitz principal
minor. -/
lemma xi_toeplitz_psd_jet_semialgebraic_cleared_minor_nonneg_iff
    (D : xi_toeplitz_psd_jet_semialgebraic_data) (m : Fin (D.N + 1)) :
    0 ≤ xi_toeplitz_psd_jet_semialgebraic_cleared_minor D m ↔
      0 ≤ xi_toeplitz_psd_jet_semialgebraic_toeplitz_det_prefix D m := by
  constructor
  · intro hCleared
    by_contra hDetNonneg
    have hDetNeg :
        xi_toeplitz_psd_jet_semialgebraic_toeplitz_det_prefix D m < 0 := lt_of_not_ge hDetNonneg
    have hClearedNeg : xi_toeplitz_psd_jet_semialgebraic_cleared_minor D m < 0 := by
      unfold xi_toeplitz_psd_jet_semialgebraic_cleared_minor
      exact mul_neg_of_pos_of_neg (pow_pos D.clearingDenominator_pos _) hDetNeg
    exact not_lt_of_ge hCleared hClearedNeg
  · intro hDetNonneg
    unfold xi_toeplitz_psd_jet_semialgebraic_cleared_minor
    exact mul_nonneg (pow_nonneg (le_of_lt D.clearingDenominator_pos) _) hDetNonneg

/-- Paper label: `cor:xi-toeplitz-psd-jet-semialgebraic`. -/
theorem paper_xi_toeplitz_psd_jet_semialgebraic
    (D : xi_toeplitz_psd_jet_semialgebraic_data) :
    xi_toeplitz_psd_jet_semialgebraic_statement D := by
  let J := xi_toeplitz_psd_jet_semialgebraic_jet_data D
  let T := xi_toeplitz_psd_jet_semialgebraic_toeplitz_data D
  have hJet := paper_xi_verblunsky_from_local_jet J
  have hLocal :=
    paper_xi_local_jet_determines_finite_cmv_and_toeplitz_certificate D.ell D.coeff
      D.coeff_zero D.coeff_one D.coeff_two D.coeff_zero_pos D.N D.delta0 D.hdelta0
  rcases hJet with ⟨_, hCoeff0, hCoeff1, _, _, _, _, hPrefix⟩
  rcases hLocal with ⟨hJet0, hJet1, hAlpha, hDet, _, _, _⟩
  refine ⟨hJet0, hJet1, ?_, hAlpha, hDet, ?_, ?_⟩
  · intro n hn
    exact hPrefix n
  · intro m
    exact xi_toeplitz_psd_jet_semialgebraic_cleared_minor_nonneg_iff D m
  · constructor
    · intro hCleared m
      exact (xi_toeplitz_psd_jet_semialgebraic_cleared_minor_nonneg_iff D m).1 (hCleared m)
    · intro hDet m
      exact (xi_toeplitz_psd_jet_semialgebraic_cleared_minor_nonneg_iff D m).2 (hDet m)

end

end Omega.Zeta
