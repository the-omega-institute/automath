import Mathlib.Tactic

namespace Omega.GU

/-- The two parity classes of a `ℤ₂`-torsor tensor power. -/
inductive OrientationTorsorClass
  | unit
  | base
  deriving DecidableEq, Repr

/-- Tensor powers of a `ℤ₂`-torsor only depend on the exponent modulo `2`. -/
def orientationTorsorClassOfExponent (n : ℕ) : OrientationTorsorClass :=
  if Odd n then .base else .unit

/-- The exponent `a_r` in the cartesian-power orientation law
`Or(S^r) ≅ Or(S)^{⊗ a_r}`. -/
def cartesianPowerOrientationExponent (d : ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | r + 2 => d * cartesianPowerOrientationExponent d (r + 1) + d ^ (r + 1)

lemma orientationTorsorClassOfExponent_eq_unit {n : ℕ} (hn : Even n) :
    orientationTorsorClassOfExponent n = .unit := by
  rcases hn with ⟨k, hk⟩
  unfold orientationTorsorClassOfExponent
  rw [hk]
  norm_num

lemma orientationTorsorClassOfExponent_eq_base {n : ℕ} (hn : Odd n) :
    orientationTorsorClassOfExponent n = .base := by
  unfold orientationTorsorClassOfExponent
  rw [if_pos hn]

lemma cartesianPowerOrientationExponent_closed_form_succ (d : ℕ) :
    ∀ n : ℕ, cartesianPowerOrientationExponent d (n + 1) = (n + 1) * d ^ n
  | 0 => by simp [cartesianPowerOrientationExponent]
  | n + 1 => by
      calc
        cartesianPowerOrientationExponent d (n + 2)
            = d * cartesianPowerOrientationExponent d (n + 1) + d ^ (n + 1) := by
                simp [cartesianPowerOrientationExponent]
        _ = d * ((n + 1) * d ^ n) + d ^ (n + 1) := by
              rw [cartesianPowerOrientationExponent_closed_form_succ d n]
        _ = (n + 1) * d ^ (n + 1) + d ^ (n + 1) := by
              rw [pow_succ]
              ring
        _ = (n + 2) * d ^ (n + 1) := by
              let u := d ^ (n + 1)
              calc
                (n + 1) * d ^ (n + 1) + d ^ (n + 1)
                    = (n + 1) * u + u := by simp [u]
                _ = (n + 1) * u + 1 * u := by rw [one_mul]
                _ = (n + 1 + 1) * u := by rw [← Nat.add_mul]
                _ = (n + 2) * u := by
                      simp
                _ = (n + 2) * d ^ (n + 1) := by simp [u]

lemma cartesianPowerOrientationExponent_closed_form (d r : ℕ) (hr : 1 ≤ r) :
    cartesianPowerOrientationExponent d r = r * d ^ (r - 1) := by
  rcases Nat.exists_eq_add_of_le hr with ⟨n, rfl⟩
  simpa [Nat.add_comm] using cartesianPowerOrientationExponent_closed_form_succ d n

lemma even_pow_of_pos {d n : ℕ} (hd : Even d) (hn : 1 ≤ n) : Even (d ^ n) := by
  rcases Nat.exists_eq_add_of_le hn with ⟨m, rfl⟩
  rcases hd with ⟨k, hk⟩
  refine ⟨d ^ m * k, ?_⟩
  calc
    d ^ (1 + m) = d ^ m * d := by simpa [Nat.add_comm] using (pow_succ d m)
    _ = d ^ m * (k + k) := by rw [hk]
    _ = d ^ m * k + d ^ m * k := by ring

/-- Cartesian powers of the orientation torsor satisfy the closed-form exponent law
`a_r = r d^(r-1)`, and the parity of that exponent collapses exactly as predicted by the paper.
    thm:bdry-orientation-cartesian-power-parity-collapse -/
theorem paper_bdry_orientation_cartesian_power_parity_collapse (d r : ℕ)
    (_hd : 1 ≤ d) (hr : 1 ≤ r) :
    cartesianPowerOrientationExponent d r = r * d ^ (r - 1) ∧
      ((Even d ∧ 2 ≤ r) →
        orientationTorsorClassOfExponent (cartesianPowerOrientationExponent d r) =
          OrientationTorsorClass.unit) ∧
      ((Odd d ∧ Even r) →
        orientationTorsorClassOfExponent (cartesianPowerOrientationExponent d r) =
          OrientationTorsorClass.unit) ∧
      ((Odd d ∧ Odd r) →
        orientationTorsorClassOfExponent (cartesianPowerOrientationExponent d r) =
          OrientationTorsorClass.base) := by
  have hclosed : cartesianPowerOrientationExponent d r = r * d ^ (r - 1) :=
    cartesianPowerOrientationExponent_closed_form d r hr
  refine ⟨hclosed, ?_, ?_, ?_⟩
  · rintro ⟨hdEven, hrTwo⟩
    have hpowEven : Even (d ^ (r - 1)) := by
      apply even_pow_of_pos hdEven
      omega
    have hexpEven : Even (r * d ^ (r - 1)) := by
      rcases hpowEven with ⟨k, hk⟩
      refine ⟨r * k, ?_⟩
      rw [hk]
      ring
    rw [hclosed]
    exact orientationTorsorClassOfExponent_eq_unit hexpEven
  · rintro ⟨hdOdd, hrEven⟩
    have hpowOdd : Odd (d ^ (r - 1)) := by
      simpa using hdOdd.pow
    have hexpEven : Even (r * d ^ (r - 1)) := by
      rcases hrEven with ⟨k, hk⟩
      refine ⟨k * d ^ (r - 1), ?_⟩
      rw [hk]
      ring
    rw [hclosed]
    exact orientationTorsorClassOfExponent_eq_unit hexpEven
  · rintro ⟨hdOdd, hrOdd⟩
    have hpowOdd : Odd (d ^ (r - 1)) := by
      simpa using hdOdd.pow
    rw [hclosed]
    exact orientationTorsorClassOfExponent_eq_base (hrOdd.mul hpowOdd)

end Omega.GU
