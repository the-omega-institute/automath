import Mathlib.Tactic

namespace Omega.Zeta

/-- Time needed to resolve the `ρ`-th layer in the dyadic model. -/
def xi_time_resolution_galois_adjunction_timeBound (ρ : ℕ) : ℕ :=
  2 * ρ

/-- Largest resolution visible within a time budget `t`. -/
def xi_time_resolution_galois_adjunction_reachableResolution (t : ℕ) : ℕ :=
  t / 2

/-- Closure on resolutions induced by passing to time and back. -/
def xi_time_resolution_galois_adjunction_resolutionClosure (ρ : ℕ) : ℕ :=
  xi_time_resolution_galois_adjunction_reachableResolution
    (xi_time_resolution_galois_adjunction_timeBound ρ)

/-- Interior operator on times induced by passing to resolution and back. -/
def xi_time_resolution_galois_adjunction_timeInterior (t : ℕ) : ℕ :=
  xi_time_resolution_galois_adjunction_timeBound
    (xi_time_resolution_galois_adjunction_reachableResolution t)

lemma xi_time_resolution_galois_adjunction_adjunction (ρ t : ℕ) :
    ρ ≤ xi_time_resolution_galois_adjunction_reachableResolution t ↔
      xi_time_resolution_galois_adjunction_timeBound ρ ≤ t := by
  unfold xi_time_resolution_galois_adjunction_reachableResolution
    xi_time_resolution_galois_adjunction_timeBound
  rw [Nat.mul_comm, ← Nat.le_div_iff_mul_le Nat.two_pos]

lemma xi_time_resolution_galois_adjunction_resolutionClosure_eq (ρ : ℕ) :
    xi_time_resolution_galois_adjunction_resolutionClosure ρ = ρ := by
  unfold xi_time_resolution_galois_adjunction_resolutionClosure
    xi_time_resolution_galois_adjunction_reachableResolution
    xi_time_resolution_galois_adjunction_timeBound
  simp

lemma xi_time_resolution_galois_adjunction_timeInterior_le (t : ℕ) :
    xi_time_resolution_galois_adjunction_timeInterior t ≤ t := by
  have h :=
    (xi_time_resolution_galois_adjunction_adjunction
      (xi_time_resolution_galois_adjunction_reachableResolution t) t).mp le_rfl
  simpa [xi_time_resolution_galois_adjunction_timeInterior] using h

lemma xi_time_resolution_galois_adjunction_timeInterior_idempotent (t : ℕ) :
    xi_time_resolution_galois_adjunction_timeInterior
        (xi_time_resolution_galois_adjunction_timeInterior t) =
      xi_time_resolution_galois_adjunction_timeInterior t := by
  unfold xi_time_resolution_galois_adjunction_timeInterior
    xi_time_resolution_galois_adjunction_timeBound
    xi_time_resolution_galois_adjunction_reachableResolution
  simp

lemma xi_time_resolution_galois_adjunction_timeInterior_fixed_iff_even (t : ℕ) :
    xi_time_resolution_galois_adjunction_timeInterior t = t ↔ Even t := by
  constructor
  · intro hfixed
    have hdecomp : t % 2 + 2 * (t / 2) = t := Nat.mod_add_div t 2
    have hmod : t % 2 = 0 := by
      have hsum :
          t % 2 + xi_time_resolution_galois_adjunction_timeInterior t = t := by
        simpa [xi_time_resolution_galois_adjunction_timeInterior] using hdecomp
      have hsum' : t % 2 + t = t := by simpa [hfixed] using hsum
      omega
    exact Nat.even_iff.mpr hmod
  · intro hEven
    have hmod : t % 2 = 0 := Nat.even_iff.mp hEven
    have hdecomp : t % 2 + 2 * (t / 2) = t := Nat.mod_add_div t 2
    simpa [xi_time_resolution_galois_adjunction_timeInterior, hmod] using hdecomp

/-- Paper label: `thm:xi-time-resolution-galois-adjunction`. The dyadic time map `ρ ↦ 2ρ` and
the reachable-resolution map `t ↦ ⌊t / 2⌋` form a concrete Galois adjunction. The induced closure
on resolutions is the identity, the induced interior on times is idempotent and below the
identity, and its fixed points are exactly the even times. -/
theorem paper_xi_time_resolution_galois_adjunction :
    (∀ ρ t,
      ρ ≤ xi_time_resolution_galois_adjunction_reachableResolution t ↔
        xi_time_resolution_galois_adjunction_timeBound ρ ≤ t) ∧
    (∀ ρ, xi_time_resolution_galois_adjunction_resolutionClosure ρ = ρ) ∧
    (∀ t, xi_time_resolution_galois_adjunction_timeInterior t ≤ t) ∧
    (∀ t,
      xi_time_resolution_galois_adjunction_timeInterior
          (xi_time_resolution_galois_adjunction_timeInterior t) =
        xi_time_resolution_galois_adjunction_timeInterior t) ∧
    (∀ t, xi_time_resolution_galois_adjunction_timeInterior t = t ↔ Even t) := by
  refine ⟨xi_time_resolution_galois_adjunction_adjunction,
    xi_time_resolution_galois_adjunction_resolutionClosure_eq,
    xi_time_resolution_galois_adjunction_timeInterior_le,
    xi_time_resolution_galois_adjunction_timeInterior_idempotent,
    xi_time_resolution_galois_adjunction_timeInterior_fixed_iff_even⟩

end Omega.Zeta
