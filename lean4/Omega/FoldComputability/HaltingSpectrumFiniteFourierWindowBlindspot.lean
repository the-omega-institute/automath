import Mathlib

namespace Omega.FoldComputability

/-- The empty halting spectrum contributes zero to every positive Fourier moment. -/
def fold_computability_halting_spectrum_finite_fourier_window_blindspot_emptyMoment
    (_n : ℕ) : ℤ :=
  0

/-- The singleton spectrum `{e}` contributes the `q e`-root moment. -/
def fold_computability_halting_spectrum_finite_fourier_window_blindspot_singletonMoment
    (q : ℕ → ℕ) (e n : ℕ) : ℤ :=
  if q e ∣ n then 1 else 0

/-- The finite Fourier observation window on the empty halting set. -/
def fold_computability_halting_spectrum_finite_fourier_window_blindspot_emptyWindow
    (N : ℕ) : Fin N → ℤ :=
  fun i =>
    fold_computability_halting_spectrum_finite_fourier_window_blindspot_emptyMoment i.1.succ

/-- The finite Fourier observation window on the singleton halting set `{e}`. -/
def fold_computability_halting_spectrum_finite_fourier_window_blindspot_singletonWindow
    (q : ℕ → ℕ) (e N : ℕ) : Fin N → ℤ :=
  fun i =>
    fold_computability_halting_spectrum_finite_fourier_window_blindspot_singletonMoment
      q e i.1.succ

lemma fold_computability_halting_spectrum_finite_fourier_window_blindspot_singletonMoment_eq_zero
    (q : ℕ → ℕ) (N e n : ℕ) (hn : 1 ≤ n) (hnN : n ≤ N) (hq : N < q e) :
    fold_computability_halting_spectrum_finite_fourier_window_blindspot_singletonMoment q e n = 0 := by
  unfold fold_computability_halting_spectrum_finite_fourier_window_blindspot_singletonMoment
  by_cases hdiv : q e ∣ n
  · have hle : q e ≤ n := Nat.le_of_dvd hn hdiv
    omega
  · simp [hdiv]

/-- Paper label: `prop:fold-computability-halting-spectrum-finite-fourier-window-blindspot`.
If `q e` lies beyond the finite observation window `1, ..., N`, then the empty halting set and the
singleton halting set `{e}` have exactly the same observed Fourier moments in that window, so any
decision rule depending only on the window returns the same output on both inputs. -/
theorem paper_fold_computability_halting_spectrum_finite_fourier_window_blindspot
    (q : ℕ → ℕ) (N e : ℕ) (_hN : 1 ≤ N) (hq : N < q e) :
    fold_computability_halting_spectrum_finite_fourier_window_blindspot_emptyWindow N =
      fold_computability_halting_spectrum_finite_fourier_window_blindspot_singletonWindow q e N ∧
    ∀ decider : (Fin N → ℤ) → Bool,
      decider
          (fold_computability_halting_spectrum_finite_fourier_window_blindspot_emptyWindow N) =
        decider
          (fold_computability_halting_spectrum_finite_fourier_window_blindspot_singletonWindow
            q e N) := by
  have hEq :
      fold_computability_halting_spectrum_finite_fourier_window_blindspot_emptyWindow N =
        fold_computability_halting_spectrum_finite_fourier_window_blindspot_singletonWindow q e N := by
    funext i
    have hi1 : 1 ≤ i.1.succ := Nat.succ_le_succ (Nat.zero_le _)
    have hiN : i.1.succ ≤ N := i.2
    have hzero :
        fold_computability_halting_spectrum_finite_fourier_window_blindspot_singletonMoment
            q e i.1.succ = 0 :=
      fold_computability_halting_spectrum_finite_fourier_window_blindspot_singletonMoment_eq_zero
        q N e i.1.succ hi1 hiN hq
    simp [fold_computability_halting_spectrum_finite_fourier_window_blindspot_emptyWindow,
      fold_computability_halting_spectrum_finite_fourier_window_blindspot_emptyMoment,
      fold_computability_halting_spectrum_finite_fourier_window_blindspot_singletonWindow, hzero]
  constructor
  · exact hEq
  · intro decider
    rw [hEq]

end Omega.FoldComputability
