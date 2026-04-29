import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete reversible-lift coding data.  A fiber of size `fiberCard` is injectively encoded by
binary side-information words of length `lengthWords`; the entropy and kappa fields record the
log-multiplicity and base-two entropy normalizations. -/
structure xi_fold_reversible_lift_length_lowerbound_kappa_data where
  xi_fold_reversible_lift_length_lowerbound_kappa_fiberCard : ℕ
  xi_fold_reversible_lift_length_lowerbound_kappa_lengthWords : ℕ
  xi_fold_reversible_lift_length_lowerbound_kappa_encode :
    Fin xi_fold_reversible_lift_length_lowerbound_kappa_fiberCard →
      Fin (2 ^ xi_fold_reversible_lift_length_lowerbound_kappa_lengthWords)
  xi_fold_reversible_lift_length_lowerbound_kappa_encode_injective :
    Function.Injective xi_fold_reversible_lift_length_lowerbound_kappa_encode
  xi_fold_reversible_lift_length_lowerbound_kappa_fiberCard_pos :
    0 < xi_fold_reversible_lift_length_lowerbound_kappa_fiberCard
  xi_fold_reversible_lift_length_lowerbound_kappa_entropy : ℝ
  xi_fold_reversible_lift_length_lowerbound_kappa_kappa : ℝ
  xi_fold_reversible_lift_length_lowerbound_kappa_entropy_eq_log_multiplicity :
    xi_fold_reversible_lift_length_lowerbound_kappa_entropy =
      Real.log xi_fold_reversible_lift_length_lowerbound_kappa_fiberCard
  xi_fold_reversible_lift_length_lowerbound_kappa_kappa_eq_entropy_bits :
    xi_fold_reversible_lift_length_lowerbound_kappa_kappa =
      xi_fold_reversible_lift_length_lowerbound_kappa_entropy / Real.log 2

namespace xi_fold_reversible_lift_length_lowerbound_kappa_data

/-- The injective side-information code forces the binary log-cardinality lower bound. -/
def lengthLowerBound
    (D : xi_fold_reversible_lift_length_lowerbound_kappa_data) : Prop :=
  Real.log D.xi_fold_reversible_lift_length_lowerbound_kappa_fiberCard / Real.log 2 ≤
    D.xi_fold_reversible_lift_length_lowerbound_kappa_lengthWords

/-- Entropy form of the same lower bound after substituting the log-multiplicity identity. -/
def entropyFormLowerBound
    (D : xi_fold_reversible_lift_length_lowerbound_kappa_data) : Prop :=
  D.xi_fold_reversible_lift_length_lowerbound_kappa_entropy / Real.log 2 ≤
    D.xi_fold_reversible_lift_length_lowerbound_kappa_lengthWords

/-- Coarse kappa-normalized lower bound. -/
def coarseLowerBound
    (D : xi_fold_reversible_lift_length_lowerbound_kappa_data) : Prop :=
  D.xi_fold_reversible_lift_length_lowerbound_kappa_kappa ≤
    D.xi_fold_reversible_lift_length_lowerbound_kappa_lengthWords

end xi_fold_reversible_lift_length_lowerbound_kappa_data

open xi_fold_reversible_lift_length_lowerbound_kappa_data

/-- Paper label: `thm:xi-fold-reversible-lift-length-lowerbound-kappa`. -/
theorem paper_xi_fold_reversible_lift_length_lowerbound_kappa
    (D : xi_fold_reversible_lift_length_lowerbound_kappa_data) :
    D.lengthLowerBound ∧ D.entropyFormLowerBound ∧ D.coarseLowerBound := by
  have hcard :
      D.xi_fold_reversible_lift_length_lowerbound_kappa_fiberCard ≤
        2 ^ D.xi_fold_reversible_lift_length_lowerbound_kappa_lengthWords := by
    simpa [Fintype.card_fin] using
      Fintype.card_le_of_injective
        D.xi_fold_reversible_lift_length_lowerbound_kappa_encode
        D.xi_fold_reversible_lift_length_lowerbound_kappa_encode_injective
  have hcardReal :
      (D.xi_fold_reversible_lift_length_lowerbound_kappa_fiberCard : ℝ) ≤
        ((2 : ℝ) ^ D.xi_fold_reversible_lift_length_lowerbound_kappa_lengthWords) := by
    exact_mod_cast hcard
  have hfiberPos :
      0 < (D.xi_fold_reversible_lift_length_lowerbound_kappa_fiberCard : ℝ) := by
    exact_mod_cast D.xi_fold_reversible_lift_length_lowerbound_kappa_fiberCard_pos
  have hlogCard :
      Real.log D.xi_fold_reversible_lift_length_lowerbound_kappa_fiberCard ≤
        D.xi_fold_reversible_lift_length_lowerbound_kappa_lengthWords * Real.log 2 := by
    calc
      Real.log D.xi_fold_reversible_lift_length_lowerbound_kappa_fiberCard ≤
          Real.log ((2 : ℝ) ^
            D.xi_fold_reversible_lift_length_lowerbound_kappa_lengthWords) := by
            exact Real.log_le_log hfiberPos hcardReal
      _ = D.xi_fold_reversible_lift_length_lowerbound_kappa_lengthWords * Real.log 2 := by
            rw [Real.log_pow]
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlength : D.lengthLowerBound := by
    exact (div_le_iff₀ hlog2).2 (by simpa [mul_comm] using hlogCard)
  have hentropy : D.entropyFormLowerBound := by
    simpa [entropyFormLowerBound,
      D.xi_fold_reversible_lift_length_lowerbound_kappa_entropy_eq_log_multiplicity] using
      hlength
  refine ⟨hlength, hentropy, ?_⟩
  simpa [coarseLowerBound,
    D.xi_fold_reversible_lift_length_lowerbound_kappa_kappa_eq_entropy_bits] using hentropy

end Omega.Zeta
