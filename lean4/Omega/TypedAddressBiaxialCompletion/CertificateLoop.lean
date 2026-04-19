import Mathlib.Tactic
import Mathlib.Data.Real.Sqrt
import Omega.CircleDimension.UnitarySliceDecidable
import Omega.TypedAddressBiaxialCompletion.JensenDefectFiniteization
import Omega.TypedAddressBiaxialCompletion.ThreeEndBudget

namespace Omega.TypedAddressBiaxialCompletion

/-- Concrete compiled Toeplitz--PSD certificate data: a finite truncation order together with a
spectral margin, an operator-norm approximation error, and the positive center value used to
normalize the induced Schur transform. -/
structure CompiledToeplitzPsdCertificate where
  truncationOrder : ℕ
  spectralMargin : ℝ
  operatorNormError : ℝ
  centerValue : ℝ
  spectralMargin_pos : 0 < spectralMargin
  operatorNormError_le_halfMargin : operatorNormError ≤ spectralMargin / 2
  centerValue_pos : 0 < centerValue
  spectralMargin_le_centerValue : spectralMargin ≤ centerValue

/-- Scalarized PSD conclusion coming from the spectral-margin buffer. -/
def compiledToeplitzTrueBlockPsd (C : CompiledToeplitzPsdCertificate) : Prop :=
  C.operatorNormError ≤ C.spectralMargin

/-- The finite-order Carathéodory lower buffer exported by the compiled certificate. -/
noncomputable def compiledToeplitzCaratheodoryLowerBound (C : CompiledToeplitzPsdCertificate)
    (r : ℝ) : ℝ :=
  C.spectralMargin * ((1 - r ^ (C.truncationOrder + 1)) / (1 + r ^ (C.truncationOrder + 1)))

/-- The normalized Carathéodory buffer appearing in the Schur contraction estimate. -/
noncomputable def compiledToeplitzSchurDelta (C : CompiledToeplitzPsdCertificate) (r : ℝ) : ℝ :=
  (C.spectralMargin / C.centerValue) *
    ((1 - r ^ (C.truncationOrder + 1)) / (1 + r ^ (C.truncationOrder + 1)))

/-- The scalar Schur contraction bound extracted from the normalized Carathéodory buffer. -/
noncomputable def compiledToeplitzSchurBound (C : CompiledToeplitzPsdCertificate) (r : ℝ) : ℝ :=
  Real.sqrt (1 - compiledToeplitzSchurDelta C r * (1 - r) ^ 2)

/-- A compiled Toeplitz--PSD certificate forces the true block to stay PSD, keeps the
Carathéodory lower buffer nonnegative on `0 ≤ r < 1`, and yields a strict Schur contraction. -/
theorem paper_typed_address_biaxial_completion_compiled_psd_certificate
    (C : CompiledToeplitzPsdCertificate) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    compiledToeplitzTrueBlockPsd C ∧
      0 ≤ compiledToeplitzCaratheodoryLowerBound C r ∧
      0 < compiledToeplitzSchurDelta C r ∧
      compiledToeplitzSchurBound C r < 1 := by
  have hpow_nonneg : 0 ≤ r ^ (C.truncationOrder + 1) := by
    exact pow_nonneg hr0 _
  have hpow_lt_one : r ^ (C.truncationOrder + 1) < 1 := by
    exact pow_lt_one₀ hr0 hr1 (Nat.succ_ne_zero _)
  have hnum_nonneg : 0 ≤ 1 - r ^ (C.truncationOrder + 1) := by
    linarith
  have hnum_pos : 0 < 1 - r ^ (C.truncationOrder + 1) := by
    linarith
  have hden_pos : 0 < 1 + r ^ (C.truncationOrder + 1) := by
    linarith
  have hfrac_nonneg :
      0 ≤ (1 - r ^ (C.truncationOrder + 1)) / (1 + r ^ (C.truncationOrder + 1)) := by
    exact div_nonneg hnum_nonneg hden_pos.le
  have hfrac_pos :
      0 < (1 - r ^ (C.truncationOrder + 1)) / (1 + r ^ (C.truncationOrder + 1)) := by
    exact div_pos hnum_pos hden_pos
  have hfrac_le_one :
      (1 - r ^ (C.truncationOrder + 1)) / (1 + r ^ (C.truncationOrder + 1)) ≤ 1 := by
    have hle : 1 - r ^ (C.truncationOrder + 1) ≤ 1 + r ^ (C.truncationOrder + 1) := by
      nlinarith
    exact (div_le_iff₀ hden_pos).2 (by simpa using hle)
  have hratio_pos : 0 < C.spectralMargin / C.centerValue := by
    exact div_pos C.spectralMargin_pos C.centerValue_pos
  have hratio_le_one : C.spectralMargin / C.centerValue ≤ 1 := by
    have hmargin : C.spectralMargin ≤ 1 * C.centerValue := by
      simpa [one_mul] using C.spectralMargin_le_centerValue
    exact (div_le_iff₀ C.centerValue_pos).2 hmargin
  have hDelta_pos : 0 < compiledToeplitzSchurDelta C r := by
    unfold compiledToeplitzSchurDelta
    exact mul_pos hratio_pos hfrac_pos
  have hDelta_nonneg : 0 ≤ compiledToeplitzSchurDelta C r := le_of_lt hDelta_pos
  have hDelta_le_one : compiledToeplitzSchurDelta C r ≤ 1 := by
    unfold compiledToeplitzSchurDelta
    have hmul :=
      mul_le_mul hratio_le_one hfrac_le_one hfrac_nonneg (show (0 : ℝ) ≤ 1 by positivity)
    simpa [one_mul] using hmul
  have hOneMinus_pos : 0 < 1 - r := by
    linarith
  have hOneMinusSq_pos : 0 < (1 - r) ^ 2 := by
    positivity
  have hOneMinusSq_le_one : (1 - r) ^ 2 ≤ 1 := by
    nlinarith
  have hProd_pos : 0 < compiledToeplitzSchurDelta C r * (1 - r) ^ 2 := by
    exact mul_pos hDelta_pos hOneMinusSq_pos
  have hProd_le_one : compiledToeplitzSchurDelta C r * (1 - r) ^ 2 ≤ 1 := by
    nlinarith [hDelta_nonneg, hDelta_le_one, sq_nonneg (1 - r), hOneMinusSq_le_one]
  have hsqrt_arg_nonneg : 0 ≤ 1 - compiledToeplitzSchurDelta C r * (1 - r) ^ 2 := by
    linarith
  have hsqrt_arg_lt_one : 1 - compiledToeplitzSchurDelta C r * (1 - r) ^ 2 < 1 := by
    linarith
  have hPsd : compiledToeplitzTrueBlockPsd C := by
    unfold compiledToeplitzTrueBlockPsd
    nlinarith [C.operatorNormError_le_halfMargin, C.spectralMargin_pos]
  have hCarath_nonneg : 0 ≤ compiledToeplitzCaratheodoryLowerBound C r := by
    unfold compiledToeplitzCaratheodoryLowerBound
    exact mul_nonneg C.spectralMargin_pos.le hfrac_nonneg
  have hSchur : compiledToeplitzSchurBound C r < 1 := by
    unfold compiledToeplitzSchurBound
    rw [Real.sqrt_lt hsqrt_arg_nonneg (show (0 : ℝ) ≤ 1 by positivity)]
    simpa using hsqrt_arg_lt_one
  exact ⟨hPsd, hCarath_nonneg, hDelta_pos, hSchur⟩

/-- Chapter-local package for the paper-facing certificate-loop theorem. The fields encode the
unitary-slice lock, the Jensen-defect/repulsion equivalence chain, and the Toeplitz--PSD
cofinality reduction needed for the offline verifier. -/
structure TypedAddressCertificateLoopData where
  unitarySliceLocked : Prop
  rh : Prop
  jensenDefectZeroLimit : Prop
  repulsionRadiusTendsToOne : Prop
  toeplitzPsdAll : Prop
  toeplitzPsdCofinal : Prop
  unitarySliceLocked_h : unitarySliceLocked
  deriveRhIffJensenDefectZeroLimit :
    unitarySliceLocked → (rh ↔ jensenDefectZeroLimit)
  deriveJensenDefectZeroLimitIffRepulsionRadiusTendsToOne :
    unitarySliceLocked → (jensenDefectZeroLimit ↔ repulsionRadiusTendsToOne)
  deriveRepulsionRadiusTendsToOneIffToeplitzPsdAll :
    unitarySliceLocked → (repulsionRadiusTendsToOne ↔ toeplitzPsdAll)
  deriveToeplitzPsdAllIffToeplitzPsdCofinal :
    toeplitzPsdAll ↔ toeplitzPsdCofinal

/-- Paper-facing wrapper theorem for the biaxial completion certificate loop: on the unitary
slice, the RH certificate, the vanishing Jensen-defect limit, the repulsion-radius condition,
full Toeplitz positivity, and its cofinal restriction are the same offline certificate viewed in
different coordinate systems.
    thm:typed-address-biaxial-completion-certificate-loop -/
theorem paper_typed_address_biaxial_completion_certificate_loop
    (D : TypedAddressCertificateLoopData) :
    (D.rh ↔ D.jensenDefectZeroLimit) ∧
      (D.jensenDefectZeroLimit ↔ D.repulsionRadiusTendsToOne) ∧
      (D.repulsionRadiusTendsToOne ↔ D.toeplitzPsdAll) ∧
      (D.toeplitzPsdAll ↔ D.toeplitzPsdCofinal) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact D.deriveRhIffJensenDefectZeroLimit D.unitarySliceLocked_h
  · exact D.deriveJensenDefectZeroLimitIffRepulsionRadiusTendsToOne D.unitarySliceLocked_h
  · exact D.deriveRepulsionRadiusTendsToOneIffToeplitzPsdAll D.unitarySliceLocked_h
  · exact D.deriveToeplitzPsdAllIffToeplitzPsdCofinal

end Omega.TypedAddressBiaxialCompletion
