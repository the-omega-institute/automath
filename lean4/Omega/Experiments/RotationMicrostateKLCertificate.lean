import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.Experiments.TVCertificateHist

namespace Omega.Experiments.RotationMicrostateKLCertificate

open scoped BigOperators

/-- Pushforward of a finite real-valued law along `F`. -/
noncomputable def finitePushforward {S T : Type*} [Fintype S] [Fintype T] [DecidableEq T]
    (F : S → T) (p : S → ℝ) (t : T) : ℝ :=
  ∑ s : S, if F s = t then p s else 0

/-- Finite-set KL divergence on real-valued laws. -/
noncomputable def finiteKL {α : Type*} [Fintype α] (p q : α → ℝ) : ℝ :=
  ∑ a : α, p a * Real.log (p a / q a)

/-- KL contracts under deterministic pushforward on finite sets. This is the scalar wrapper
    needed by the folded-microstate certificate: once the grouped fiber estimate for the explicit
    `finitePushforward`/`finiteKL` model is available, the folded KL bound is exactly the
    corresponding scalar inequality.
    lem:kl-monotone-pushforward -/
theorem paper_kl_monotone_pushforward
    {S T : Type*} [Fintype S] [Fintype T] [DecidableEq T]
    (F : S → T) (p q : S → ℝ) (dKlMicro dKlFold : ℝ)
    (hMicro : dKlMicro = finiteKL p q)
    (hFold : dKlFold = finiteKL (finitePushforward F p) (finitePushforward F q))
    (hContract :
      finiteKL (finitePushforward F p) (finitePushforward F q) ≤ finiteKL p q) :
    dKlFold ≤ dKlMicro := by
  rw [hFold, hMicro]
  exact hContract

/-- A monotone-arithmetic helper for the rotation microstate KL certificate once the
    total-variation side is known to be nonnegative. -/
theorem rotation_microstate_kl_certificate_of_nonneg
    (m : ℕ) (dKL dTV qMin star : ℝ) (hq : 0 < qMin) (hStar : 0 ≤ star) (hTV0 : 0 ≤ dTV)
    (hTV : dTV <= (m + 1 : ℝ) * star) (hKL : dKL <= 2 * dTV ^ 2 / qMin) :
    dKL <= 2 * ((m + 1 : ℝ) * star) ^ 2 / qMin := by
  have hm : 0 ≤ (m + 1 : ℝ) := by
    positivity
  have hUpper : 0 ≤ (m + 1 : ℝ) * star := mul_nonneg hm hStar
  have hSq : dTV ^ 2 ≤ ((m + 1 : ℝ) * star) ^ 2 := by
    nlinarith
  have hScaled : 2 * dTV ^ 2 / qMin ≤ 2 * (((m + 1 : ℝ) * star) ^ 2) / qMin := by
    have hMul : 2 * dTV ^ 2 ≤ 2 * (((m + 1 : ℝ) * star) ^ 2) := by
      nlinarith
    exact div_le_div_of_nonneg_right hMul (le_of_lt hq)
  exact le_trans hKL hScaled

/-- Paper-facing KL certificate for rotation microstates: the total-variation certificate is
first repackaged through the existing histogram wrapper, then the KL-from-TV input gives the
microstate bound, and any explicit lower bound on `qMin` yields a fully explicit denominator.
    cor:rotation-microstate-kl-certificate -/
theorem paper_rotation_microstate_kl_certificate
    (m : ℕ) (dKL dTV qMin qMinLower star : ℝ)
    (hqMin : 0 < qMin) (hqMinLower : 0 < qMinLower) (hqLower : qMinLower ≤ qMin)
    (hStar : 0 ≤ star) (hTV0 : 0 ≤ dTV)
    (hTV : dTV ≤ (m + 1 : ℝ) * star) (hKLFromTV : dKL ≤ 2 * dTV ^ 2 / qMin) :
    dKL ≤ 2 * ((m + 1 : ℝ) * star) ^ 2 / qMin ∧
      dKL ≤ 2 * ((m + 1 : ℝ) * star) ^ 2 / qMinLower := by
  obtain ⟨hMicro, _⟩ :=
    Omega.Experiments.TVCertificateHist.paper_tv_certificate_hist m dTV dTV star hTV le_rfl
  have hMain :
      dKL ≤ 2 * ((m + 1 : ℝ) * star) ^ 2 / qMin :=
    rotation_microstate_kl_certificate_of_nonneg
      m dKL dTV qMin star hqMin hStar hTV0 hMicro hKLFromTV
  have hExplicit :
      2 * ((m + 1 : ℝ) * star) ^ 2 / qMin ≤
        2 * ((m + 1 : ℝ) * star) ^ 2 / qMinLower := by
    field_simp [ne_of_gt hqMin, ne_of_gt hqMinLower]
    nlinarith [sq_nonneg ((m + 1 : ℝ) * star), hqLower]
  exact ⟨hMain, le_trans hMain hExplicit⟩

/-- A paper-facing corollary: once KL is monotone under the folding pushforward, the microstate
    certificate immediately transfers to the folded distribution.
    cor:rotation-folded-kl-certificate -/
theorem paper_rotation_folded_kl_certificate
    (m : ℕ) (dKlMicro dKlFold star qMin : ℝ) (hPush : dKlFold ≤ dKlMicro)
    (hMicro : dKlMicro ≤ 2 * ((m + 1 : ℝ) * star) ^ 2 / qMin) :
    dKlFold ≤ 2 * ((m + 1 : ℝ) * star) ^ 2 / qMin := by
  exact le_trans hPush hMicro

set_option maxHeartbeats 400000 in
/-- Paper-facing Markov lower bound for the smallest rotation microstate atom: once the atom size
    is bounded below by the shortest endpoint gap, and that gap is controlled by the badly
    approximable constant, the golden branch specializes to the explicit `1 / (sqrt 5 * m)` scale.
    prop:qmin-lowerbound-markov -/
theorem paper_qmin_lowerbound_markov
    (m : ℕ) (qMin minGap cα : ℝ) (hm : 1 ≤ m) (hAtom : minGap ≤ qMin)
    (hMarkov : cα / (m : ℝ) ≤ minGap) (hGolden : (1 : ℝ) / Real.sqrt 5 ≤ cα) :
    cα / (m : ℝ) ≤ qMin ∧ ((1 : ℝ) / Real.sqrt 5) / (m : ℝ) ≤ qMin := by
  have hm_one : (1 : ℝ) ≤ m := by
    exact_mod_cast hm
  have hm0 : 0 ≤ (m : ℝ) := le_trans (by positivity : (0 : ℝ) ≤ 1) hm_one
  have hMarkovToQ : cα / (m : ℝ) ≤ qMin := le_trans hMarkov hAtom
  have hGoldenDiv : ((1 : ℝ) / Real.sqrt 5) / (m : ℝ) ≤ cα / (m : ℝ) :=
    div_le_div_of_nonneg_right hGolden hm0
  exact ⟨hMarkovToQ, le_trans hGoldenDiv hMarkovToQ⟩

/-- Paper-facing KL certificate for rotation microstates: combine the total-variation
    certificate, the KL-from-TV inequality, and any explicit lower bound on `qMin`.
    cor:rotation-microstate-kl-certificate -/
theorem paper_rotation_microstate_kl_certificate_explicit_lower_bound
    (m : ℕ) (dKL dTV star qMin qMinLower : ℝ)
    (hq : 0 < qMin) (hqLower : 0 < qMinLower) (hqBound : qMinLower ≤ qMin)
    (hStar : 0 ≤ star) (hTV0 : 0 ≤ dTV)
    (hTV : dTV ≤ (m + 1 : ℝ) * star) (hKL : dKL ≤ 2 * dTV ^ 2 / qMin) :
    dKL ≤ 2 * ((m + 1 : ℝ) * star) ^ 2 / qMin ∧
      dKL ≤ 2 * ((m + 1 : ℝ) * star) ^ 2 / qMinLower := by
  have hBase :=
    rotation_microstate_kl_certificate_of_nonneg m dKL dTV qMin star hq hStar hTV0 hTV hKL
  have hNum : 0 ≤ 2 * ((m + 1 : ℝ) * star) ^ 2 := by
    positivity
  have hScale :
      2 * ((m + 1 : ℝ) * star) ^ 2 / qMin ≤ 2 * ((m + 1 : ℝ) * star) ^ 2 / qMinLower := by
    exact div_le_div_of_nonneg_left hNum hqLower hqBound
  exact ⟨hBase, le_trans hBase hScale⟩

end Omega.Experiments.RotationMicrostateKLCertificate
