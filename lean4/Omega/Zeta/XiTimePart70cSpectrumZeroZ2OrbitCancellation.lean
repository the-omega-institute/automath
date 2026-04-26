import Mathlib

namespace Omega.Zeta

open scoped BigOperators

/-- The coordinate involution flipping the `j`-th Boolean coordinate. -/
def xi_time_part70c_spectrum_zero_z2_orbit_cancellation_toggle {m : ℕ}
    (j : Fin m) (ω : Fin m → Bool) : Fin m → Bool :=
  Function.update ω j (!(ω j))

/-- The sign factor attached to one Boolean coordinate. -/
def xi_time_part70c_spectrum_zero_z2_orbit_cancellation_phaseBit (b : Bool) : ℤ :=
  if b then -1 else 1

/-- The orbit phase obtained by multiplying the coordinate signs across the selected zero set. -/
def xi_time_part70c_spectrum_zero_z2_orbit_cancellation_phase {m : ℕ}
    (J : Finset (Fin m)) (ω : Fin m → Bool) : ℤ :=
  Finset.prod J fun j => xi_time_part70c_spectrum_zero_z2_orbit_cancellation_phaseBit (ω j)

private lemma xi_time_part70c_spectrum_zero_z2_orbit_cancellation_toggle_involutive {m : ℕ}
    (j : Fin m) (ω : Fin m → Bool) :
    xi_time_part70c_spectrum_zero_z2_orbit_cancellation_toggle j
        (xi_time_part70c_spectrum_zero_z2_orbit_cancellation_toggle j ω) = ω := by
  ext i
  by_cases hi : i = j
  · subst hi
    simp [xi_time_part70c_spectrum_zero_z2_orbit_cancellation_toggle]
  · simp [xi_time_part70c_spectrum_zero_z2_orbit_cancellation_toggle, hi]

private lemma xi_time_part70c_spectrum_zero_z2_orbit_cancellation_toggle_comm {m : ℕ}
    {j j' : Fin m} (hjj' : j ≠ j') (ω : Fin m → Bool) :
    xi_time_part70c_spectrum_zero_z2_orbit_cancellation_toggle j
        (xi_time_part70c_spectrum_zero_z2_orbit_cancellation_toggle j' ω) =
      xi_time_part70c_spectrum_zero_z2_orbit_cancellation_toggle j'
        (xi_time_part70c_spectrum_zero_z2_orbit_cancellation_toggle j ω) := by
  ext i
  by_cases hi : i = j
  · subst hi
    simp [xi_time_part70c_spectrum_zero_z2_orbit_cancellation_toggle, hjj']
  · by_cases hi' : i = j'
    · subst hi'
      simp [xi_time_part70c_spectrum_zero_z2_orbit_cancellation_toggle, hi, hjj']
    · simp [xi_time_part70c_spectrum_zero_z2_orbit_cancellation_toggle, hi, hi']

private lemma xi_time_part70c_spectrum_zero_z2_orbit_cancellation_toggle_free {m : ℕ}
    (j : Fin m) (ω : Fin m → Bool) :
    xi_time_part70c_spectrum_zero_z2_orbit_cancellation_toggle j ω ≠ ω := by
  intro h
  have hj := congrArg (fun f => f j) h
  simp [xi_time_part70c_spectrum_zero_z2_orbit_cancellation_toggle] at hj

private lemma xi_time_part70c_spectrum_zero_z2_orbit_cancellation_phaseBit_flip (b : Bool) :
    xi_time_part70c_spectrum_zero_z2_orbit_cancellation_phaseBit (!b) =
      -xi_time_part70c_spectrum_zero_z2_orbit_cancellation_phaseBit b := by
  cases b <;> simp [xi_time_part70c_spectrum_zero_z2_orbit_cancellation_phaseBit]

private lemma xi_time_part70c_spectrum_zero_z2_orbit_cancellation_phase_flip {m : ℕ}
    (J : Finset (Fin m)) {j : Fin m} (hj : j ∈ J) (ω : Fin m → Bool) :
    xi_time_part70c_spectrum_zero_z2_orbit_cancellation_phase J
        (xi_time_part70c_spectrum_zero_z2_orbit_cancellation_toggle j ω) =
      -xi_time_part70c_spectrum_zero_z2_orbit_cancellation_phase J ω := by
  rw [xi_time_part70c_spectrum_zero_z2_orbit_cancellation_phase,
    xi_time_part70c_spectrum_zero_z2_orbit_cancellation_phase,
    ← Finset.insert_erase hj, Finset.prod_insert (by simp [hj]),
    ← Finset.insert_erase hj, Finset.prod_insert (by simp [hj])]
  have htail :
      Finset.prod (J.erase j) (fun x =>
        xi_time_part70c_spectrum_zero_z2_orbit_cancellation_phaseBit
          ((xi_time_part70c_spectrum_zero_z2_orbit_cancellation_toggle j ω) x)) =
        Finset.prod (J.erase j) fun x =>
          xi_time_part70c_spectrum_zero_z2_orbit_cancellation_phaseBit (ω x) := by
    refine Finset.prod_congr rfl ?_
    intro x hx
    have hxj : x ≠ j := by
      exact Finset.mem_erase.mp hx |>.1
    simp [xi_time_part70c_spectrum_zero_z2_orbit_cancellation_toggle, hxj]
  have htail' :
      ∏ x ∈ (insert j (J.erase j)).erase j,
          xi_time_part70c_spectrum_zero_z2_orbit_cancellation_phaseBit
            ((xi_time_part70c_spectrum_zero_z2_orbit_cancellation_toggle j ω) x) =
        ∏ x ∈ (insert j (J.erase j)).erase j,
          xi_time_part70c_spectrum_zero_z2_orbit_cancellation_phaseBit (ω x) := by
    simpa [Finset.erase_insert, hj] using htail
  have hhead :
      xi_time_part70c_spectrum_zero_z2_orbit_cancellation_phaseBit
          ((xi_time_part70c_spectrum_zero_z2_orbit_cancellation_toggle j ω) j) =
        -xi_time_part70c_spectrum_zero_z2_orbit_cancellation_phaseBit (ω j) := by
    simp [xi_time_part70c_spectrum_zero_z2_orbit_cancellation_toggle,
      xi_time_part70c_spectrum_zero_z2_orbit_cancellation_phaseBit_flip]
  rw [htail', hhead]
  ring

/-- Paper label: `thm:xi-time-part70c-spectrum-zero-z2-orbit-cancellation`.

On the Boolean cube, the coordinate flips indexed by a nonempty zero set `J` are commuting free
involutions. Their common sign character is the product phase across `J`, and summing that
character over the whole `J`-orbit gives zero. -/
theorem paper_xi_time_part70c_spectrum_zero_z2_orbit_cancellation {m : ℕ}
    (J : Finset (Fin m)) (ω : Fin m → Bool) (hJ : J.Nonempty) :
    (∀ j ∈ J,
      xi_time_part70c_spectrum_zero_z2_orbit_cancellation_toggle j
          (xi_time_part70c_spectrum_zero_z2_orbit_cancellation_toggle j ω) = ω) ∧
    (∀ j ∈ J, ∀ j' ∈ J, j ≠ j' →
      xi_time_part70c_spectrum_zero_z2_orbit_cancellation_toggle j
          (xi_time_part70c_spectrum_zero_z2_orbit_cancellation_toggle j' ω) =
        xi_time_part70c_spectrum_zero_z2_orbit_cancellation_toggle j'
          (xi_time_part70c_spectrum_zero_z2_orbit_cancellation_toggle j ω)) ∧
    (∀ j ∈ J,
      xi_time_part70c_spectrum_zero_z2_orbit_cancellation_toggle j ω ≠ ω) ∧
    (∀ j ∈ J,
      xi_time_part70c_spectrum_zero_z2_orbit_cancellation_phase J
          (xi_time_part70c_spectrum_zero_z2_orbit_cancellation_toggle j ω) =
        -xi_time_part70c_spectrum_zero_z2_orbit_cancellation_phase J ω) ∧
    (Finset.sum J.powerset (fun S =>
      ((-1 : ℤ) ^ S.card) *
        xi_time_part70c_spectrum_zero_z2_orbit_cancellation_phase J ω)) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    exact xi_time_part70c_spectrum_zero_z2_orbit_cancellation_toggle_involutive j ω
  · intro j hj j' hj' hjj'
    exact xi_time_part70c_spectrum_zero_z2_orbit_cancellation_toggle_comm hjj' ω
  · intro j hj
    exact xi_time_part70c_spectrum_zero_z2_orbit_cancellation_toggle_free j ω
  · intro j hj
    exact xi_time_part70c_spectrum_zero_z2_orbit_cancellation_phase_flip J hj ω
  · have hsum :
        Finset.sum J.powerset (fun S => (-1 : ℤ) ^ S.card) = 0 := by
      simpa using Finset.sum_powerset_neg_one_pow_card_of_nonempty (x := J) hJ
    calc
      Finset.sum J.powerset (fun S =>
          ((-1 : ℤ) ^ S.card) *
            xi_time_part70c_spectrum_zero_z2_orbit_cancellation_phase J ω) =
        Finset.sum J.powerset (fun S => (-1 : ℤ) ^ S.card) *
          xi_time_part70c_spectrum_zero_z2_orbit_cancellation_phase J ω := by
            simpa [mul_comm, mul_left_comm, mul_assoc] using
              (Finset.mul_sum (s := J.powerset)
                (f := fun S : Finset (Fin m) => (-1 : ℤ) ^ S.card)
                (a := xi_time_part70c_spectrum_zero_z2_orbit_cancellation_phase J ω)).symm
      _ = 0 := by simp [hsum]

end Omega.Zeta
