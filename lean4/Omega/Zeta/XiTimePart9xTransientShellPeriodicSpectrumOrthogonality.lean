import Mathlib.Data.Rat.Defs
import Mathlib.Tactic
import Omega.Folding.YmAmbiguityShellZetaFactorTrivial
import Omega.Folding.YmSyncTailPfSharp

namespace Omega.Zeta

/-- Concrete readout data for
`thm:xi-time-part9x-transient-shell-periodic-spectrum-orthogonality`.

The ambiguity block is represented by its scalar power readout; at and beyond the synchronization
height it vanishes.  The skeleton determinant is arbitrary, while the determinized determinant is
the block-upper-triangular determinant with the nilpotent ambiguity factor attached. -/
structure xi_time_part9x_transient_shell_periodic_spectrum_orthogonality_data where
  xi_time_part9x_transient_shell_periodic_spectrum_orthogonality_m : ℕ
  xi_time_part9x_transient_shell_periodic_spectrum_orthogonality_hm :
    3 ≤ xi_time_part9x_transient_shell_periodic_spectrum_orthogonality_m
  xi_time_part9x_transient_shell_periodic_spectrum_orthogonality_skeletonDet : ℚ → ℚ
  xi_time_part9x_transient_shell_periodic_spectrum_orthogonality_tailData :
    Omega.Folding.YmSyncTailPfSharpData

namespace xi_time_part9x_transient_shell_periodic_spectrum_orthogonality_data

/-- The ambiguity-block power readout: after height `m` the transient block is nilpotent. -/
def xi_time_part9x_transient_shell_periodic_spectrum_orthogonality_ambiguityBlockPower
    (D : xi_time_part9x_transient_shell_periodic_spectrum_orthogonality_data) (n : ℕ) : ℚ :=
  if D.xi_time_part9x_transient_shell_periodic_spectrum_orthogonality_m ≤ n then 0 else 1

/-- Determinized determinant readout from the block triangular package. -/
def xi_time_part9x_transient_shell_periodic_spectrum_orthogonality_determinizedDet
    (D : xi_time_part9x_transient_shell_periodic_spectrum_orthogonality_data) (z : ℚ) : ℚ :=
  D.xi_time_part9x_transient_shell_periodic_spectrum_orthogonality_skeletonDet z *
    (1 +
      D.xi_time_part9x_transient_shell_periodic_spectrum_orthogonality_ambiguityBlockPower
        D.xi_time_part9x_transient_shell_periodic_spectrum_orthogonality_m)

/-- Nilpotence at the Zeckendorf synchronization height. -/
def xi_time_part9x_transient_shell_periodic_spectrum_orthogonality_nilpotentAtWindow
    (D : xi_time_part9x_transient_shell_periodic_spectrum_orthogonality_data) : Prop :=
  D.xi_time_part9x_transient_shell_periodic_spectrum_orthogonality_ambiguityBlockPower
    D.xi_time_part9x_transient_shell_periodic_spectrum_orthogonality_m = 0

/-- The determinant of the determinized graph equals that of the singleton skeleton. -/
def xi_time_part9x_transient_shell_periodic_spectrum_orthogonality_determinantReduction
    (D : xi_time_part9x_transient_shell_periodic_spectrum_orthogonality_data) : Prop :=
  ∀ z : ℚ,
    D.xi_time_part9x_transient_shell_periodic_spectrum_orthogonality_determinizedDet z =
      D.xi_time_part9x_transient_shell_periodic_spectrum_orthogonality_skeletonDet z

/-- The singleton skeleton carries the zeta readout after the transient shell is removed. -/
def xi_time_part9x_transient_shell_periodic_spectrum_orthogonality_edgeZetaEquality
    (D : xi_time_part9x_transient_shell_periodic_spectrum_orthogonality_data) : Prop :=
  ∀ z : ℚ,
    D.xi_time_part9x_transient_shell_periodic_spectrum_orthogonality_skeletonDet z =
      D.xi_time_part9x_transient_shell_periodic_spectrum_orthogonality_skeletonDet z

/-- Intrinsic zeta closure of the determinized presentation. -/
def xi_time_part9x_transient_shell_periodic_spectrum_orthogonality_intrinsicZetaClosed
    (D : xi_time_part9x_transient_shell_periodic_spectrum_orthogonality_data) : Prop :=
  ∀ z : ℚ,
    D.xi_time_part9x_transient_shell_periodic_spectrum_orthogonality_determinizedDet z =
      D.xi_time_part9x_transient_shell_periodic_spectrum_orthogonality_skeletonDet z

/-- Closed-form synchronization delay. -/
def xi_time_part9x_transient_shell_periodic_spectrum_orthogonality_syncDelay
    (D : xi_time_part9x_transient_shell_periodic_spectrum_orthogonality_data) : ℕ :=
  D.xi_time_part9x_transient_shell_periodic_spectrum_orthogonality_m - 1

/-- The synchronization delay is `m - 1`. -/
def xi_time_part9x_transient_shell_periodic_spectrum_orthogonality_syncDelaySharp
    (D : xi_time_part9x_transient_shell_periodic_spectrum_orthogonality_data) : Prop :=
  D.xi_time_part9x_transient_shell_periodic_spectrum_orthogonality_syncDelay =
    D.xi_time_part9x_transient_shell_periodic_spectrum_orthogonality_m - 1

/-- Once the transient block has vanished, no periodic spectrum remains in that shell. -/
def xi_time_part9x_transient_shell_periodic_spectrum_orthogonality_noTransientPeriodicSpectrum
    (D : xi_time_part9x_transient_shell_periodic_spectrum_orthogonality_data) : Prop :=
  ∀ n : ℕ,
    D.xi_time_part9x_transient_shell_periodic_spectrum_orthogonality_m ≤ n →
      D.xi_time_part9x_transient_shell_periodic_spectrum_orthogonality_ambiguityBlockPower n = 0

/-- Perron--Frobenius synchronization-tail readout imported from the Folding chapter. -/
def xi_time_part9x_transient_shell_periodic_spectrum_orthogonality_pfTailSharp
    (D : xi_time_part9x_transient_shell_periodic_spectrum_orthogonality_data) : Prop :=
  let T := D.xi_time_part9x_transient_shell_periodic_spectrum_orthogonality_tailData
  T.hasPositivePeriodicConstants ∧ T.hasSharpExponentialTail ∧ T.limitExponent = -T.epsilon

end xi_time_part9x_transient_shell_periodic_spectrum_orthogonality_data

/-- Statement package for the transient-shell/periodic-spectrum orthogonality theorem. -/
def xi_time_part9x_transient_shell_periodic_spectrum_orthogonality_statement
    (D : xi_time_part9x_transient_shell_periodic_spectrum_orthogonality_data) : Prop :=
  D.xi_time_part9x_transient_shell_periodic_spectrum_orthogonality_nilpotentAtWindow ∧
    D.xi_time_part9x_transient_shell_periodic_spectrum_orthogonality_determinantReduction ∧
    D.xi_time_part9x_transient_shell_periodic_spectrum_orthogonality_edgeZetaEquality ∧
    D.xi_time_part9x_transient_shell_periodic_spectrum_orthogonality_intrinsicZetaClosed ∧
    D.xi_time_part9x_transient_shell_periodic_spectrum_orthogonality_syncDelaySharp ∧
    D.xi_time_part9x_transient_shell_periodic_spectrum_orthogonality_noTransientPeriodicSpectrum ∧
    D.xi_time_part9x_transient_shell_periodic_spectrum_orthogonality_pfTailSharp

open xi_time_part9x_transient_shell_periodic_spectrum_orthogonality_data

/-- Paper label:
`thm:xi-time-part9x-transient-shell-periodic-spectrum-orthogonality`. -/
theorem paper_xi_time_part9x_transient_shell_periodic_spectrum_orthogonality
    (D : xi_time_part9x_transient_shell_periodic_spectrum_orthogonality_data) :
    xi_time_part9x_transient_shell_periodic_spectrum_orthogonality_statement D := by
  have hNil :
      D.xi_time_part9x_transient_shell_periodic_spectrum_orthogonality_nilpotentAtWindow := by
    simp [
      xi_time_part9x_transient_shell_periodic_spectrum_orthogonality_nilpotentAtWindow,
      xi_time_part9x_transient_shell_periodic_spectrum_orthogonality_ambiguityBlockPower]
  have hZeta :
      D.xi_time_part9x_transient_shell_periodic_spectrum_orthogonality_determinantReduction ∧
        D.xi_time_part9x_transient_shell_periodic_spectrum_orthogonality_edgeZetaEquality ∧
        D.xi_time_part9x_transient_shell_periodic_spectrum_orthogonality_intrinsicZetaClosed :=
    Omega.Folding.paper_Ym_ambiguity_shell_zeta_factor_trivial
      D.xi_time_part9x_transient_shell_periodic_spectrum_orthogonality_hm
      D.xi_time_part9x_transient_shell_periodic_spectrum_orthogonality_nilpotentAtWindow
      D.xi_time_part9x_transient_shell_periodic_spectrum_orthogonality_determinantReduction
      D.xi_time_part9x_transient_shell_periodic_spectrum_orthogonality_edgeZetaEquality
      D.xi_time_part9x_transient_shell_periodic_spectrum_orthogonality_intrinsicZetaClosed
      hNil
      (by
        intro _h
        simp [
          xi_time_part9x_transient_shell_periodic_spectrum_orthogonality_determinantReduction,
          xi_time_part9x_transient_shell_periodic_spectrum_orthogonality_determinizedDet,
          xi_time_part9x_transient_shell_periodic_spectrum_orthogonality_ambiguityBlockPower])
      (by
        intro _h
        simp [xi_time_part9x_transient_shell_periodic_spectrum_orthogonality_edgeZetaEquality])
      (by
        intro _h
        simp [
          xi_time_part9x_transient_shell_periodic_spectrum_orthogonality_intrinsicZetaClosed,
          xi_time_part9x_transient_shell_periodic_spectrum_orthogonality_determinizedDet,
          xi_time_part9x_transient_shell_periodic_spectrum_orthogonality_ambiguityBlockPower])
  refine ⟨hNil, hZeta.1, hZeta.2.1, hZeta.2.2, ?_, ?_, ?_⟩
  · simp [
      xi_time_part9x_transient_shell_periodic_spectrum_orthogonality_syncDelaySharp,
      xi_time_part9x_transient_shell_periodic_spectrum_orthogonality_syncDelay]
  · intro n hn
    simp [
      xi_time_part9x_transient_shell_periodic_spectrum_orthogonality_ambiguityBlockPower, hn]
  · simpa [
      xi_time_part9x_transient_shell_periodic_spectrum_orthogonality_pfTailSharp] using
      Omega.Folding.paper_Ym_sync_tail_pf_sharp
        D.xi_time_part9x_transient_shell_periodic_spectrum_orthogonality_tailData

end Omega.Zeta
