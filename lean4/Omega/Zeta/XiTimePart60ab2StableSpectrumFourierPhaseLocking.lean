import Omega.Zeta.XiTimePart60ab2StableSpectrumSelfreciprocalCenter
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ZMod.Basic

namespace Omega.Zeta

open scoped BigOperators ComplexConjugate

/-- Paper label: `thm:xi-time-part60ab2-stable-spectrum-fourier-phase-locking`.
The finite multiplicity attached to a stable residue class. -/
noncomputable def xi_time_part60ab2_stable_spectrum_fourier_phase_locking_multiplicity
    (m : ℕ) (r : ZMod (Nat.fib (m + 2))) : ℕ :=
  ((Finset.powerset (Finset.range m)).filter
      (fun S =>
        ((S.sum (fun j => Nat.fib (j + 2)) : ℕ) : ZMod (Nat.fib (m + 2))) = r)).card

/-- Paper label: `thm:xi-time-part60ab2-stable-spectrum-fourier-phase-locking`.
The center of the finite self-reciprocal spectrum. -/
def xi_time_part60ab2_stable_spectrum_fourier_phase_locking_center
    (m : ℕ) : ZMod (Nat.fib (m + 2)) :=
  ((Finset.range m).sum (fun j => Nat.fib (j + 2)) : ℕ)

/-- Paper label: `thm:xi-time-part60ab2-stable-spectrum-fourier-phase-locking`.
Finite Fourier coefficient against a character-like phase table. -/
noncomputable def xi_time_part60ab2_stable_spectrum_fourier_phase_locking_coefficient
    (m : ℕ) (phase : ZMod (Nat.fib (m + 2)) → ℂ) : ℂ :=
  letI : NeZero (Nat.fib (m + 2)) := ⟨Nat.ne_of_gt (Nat.fib_pos.mpr (by omega))⟩
  ∑ r : ZMod (Nat.fib (m + 2)),
    (xi_time_part60ab2_stable_spectrum_fourier_phase_locking_multiplicity m r : ℂ) * phase r

/-- Paper label: `thm:xi-time-part60ab2-stable-spectrum-fourier-phase-locking`.
Every finite Fourier coefficient is locked to the self-reciprocal center. -/
noncomputable def xi_time_part60ab2_stable_spectrum_fourier_phase_locking_statement : Prop :=
  ∀ (m : ℕ) (phase : ZMod (Nat.fib (m + 2)) → ℂ),
    letI : NeZero (Nat.fib (m + 2)) := ⟨Nat.ne_of_gt (Nat.fib_pos.mpr (by omega))⟩
    (∀ a r : ZMod (Nat.fib (m + 2)),
      phase (a - r) = phase a * conj (phase r)) →
      xi_time_part60ab2_stable_spectrum_fourier_phase_locking_coefficient m phase =
        phase (xi_time_part60ab2_stable_spectrum_fourier_phase_locking_center m) *
          conj (xi_time_part60ab2_stable_spectrum_fourier_phase_locking_coefficient m phase)

/-- Paper label: `thm:xi-time-part60ab2-stable-spectrum-fourier-phase-locking`. -/
theorem paper_xi_time_part60ab2_stable_spectrum_fourier_phase_locking :
    xi_time_part60ab2_stable_spectrum_fourier_phase_locking_statement := by
  classical
  intro m phase hphase
  let M : ℕ := Nat.fib (m + 2)
  have hM_pos : 0 < M := by
    dsimp [M]
    exact Nat.fib_pos.mpr (by omega)
  letI : NeZero M := ⟨Nat.ne_of_gt hM_pos⟩
  let Sigma : ZMod M :=
    xi_time_part60ab2_stable_spectrum_fourier_phase_locking_center m
  let d : ZMod M → ℕ :=
    xi_time_part60ab2_stable_spectrum_fourier_phase_locking_multiplicity m
  let tau : ZMod M ≃ ZMod M :=
    { toFun := fun r => Sigma - r
      invFun := fun r => Sigma - r
      left_inv := by
        intro r
        dsimp
        abel
      right_inv := by
        intro r
        dsimp
        abel }
  have hcenter :=
    paper_xi_time_part60ab2_stable_spectrum_selfreciprocal_center m
  have hsym : ∀ r : ZMod M, d r = d (Sigma - r) := by
    intro r
    simpa [d, Sigma, M,
      xi_time_part60ab2_stable_spectrum_fourier_phase_locking_multiplicity,
      xi_time_part60ab2_stable_spectrum_fourier_phase_locking_center] using hcenter r
  calc
    xi_time_part60ab2_stable_spectrum_fourier_phase_locking_coefficient m phase
        = ∑ r : ZMod M, (d (tau r) : ℂ) * phase (tau r) := by
            symm
            simpa [xi_time_part60ab2_stable_spectrum_fourier_phase_locking_coefficient,
              d, tau, M] using
              (Equiv.sum_comp tau (fun r : ZMod M => (d r : ℂ) * phase r))
    _ = ∑ r : ZMod M, (d r : ℂ) * phase (Sigma - r) := by
            refine Finset.sum_congr rfl ?_
            intro r _
            simp [tau, hsym r]
    _ = ∑ r : ZMod M, (d r : ℂ) * (phase Sigma * conj (phase r)) := by
            refine Finset.sum_congr rfl ?_
            intro r _
            rw [hphase Sigma r]
    _ = phase Sigma * ∑ r : ZMod M, (d r : ℂ) * conj (phase r) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro r _
            ring
    _ = phase Sigma *
          conj (xi_time_part60ab2_stable_spectrum_fourier_phase_locking_coefficient m phase) := by
            congr 1
            simp [xi_time_part60ab2_stable_spectrum_fourier_phase_locking_coefficient, d, M,
              map_sum, map_mul]

end Omega.Zeta
