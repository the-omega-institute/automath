import Mathlib.Tactic

namespace Omega.Zeta

/-- The dual additive datum of a torus-input map is divisible by every power of `p`. -/
def localizedSolenoidDualDivisibleAtPrime (p : Nat) {d : Nat} (x : Fin d → ℤ) : Prop :=
  ∀ n : Nat, ∃ y : Fin d → ℤ, x = (p ^ n : ℤ) • y

private theorem int_eq_zero_of_dvd_all_powers {p : Nat} (hp : 2 ≤ p) {x : ℤ}
    (hdiv : ∀ n : Nat, ((p ^ n : ℕ) : ℤ) ∣ x) : x = 0 := by
  by_contra hx
  let n : Nat := Int.natAbs x + 1
  have hle : Int.natAbs (((p ^ n : ℕ) : ℤ)) ≤ Int.natAbs x :=
    Int.natAbs_le_of_dvd_ne_zero (hdiv n) hx
  have hlt_nat : Int.natAbs x < p ^ n := by
    have hlt_succ : Int.natAbs x < Int.natAbs x + 1 := by simp
    have hpow : n < p ^ n := by
      exact n.lt_pow_self (by omega)
    simpa [n] using lt_trans hlt_succ hpow
  have hlt : Int.natAbs x < Int.natAbs (((p ^ n : ℕ) : ℤ)) := by
    simpa using hlt_nat
  exact (not_lt_of_ge hle) hlt

private theorem vector_eq_zero_of_dvd_all_powers {p d : Nat} (hp : 2 ≤ p) {x : Fin d → ℤ}
    (hdiv : localizedSolenoidDualDivisibleAtPrime p x) : x = 0 := by
  ext i
  apply int_eq_zero_of_dvd_all_powers hp
  intro n
  rcases hdiv n with ⟨y, hy⟩
  refine ⟨y i, ?_⟩
  simpa [Pi.smul_apply, zsmul_eq_mul] using congrArg (fun f => f i) hy

/-- Paper-facing surrogate statement: for any prime direction `p ∈ S`, a dual map from the
localized additive group into `ℤ^d` that is divisible by every power of `p` must vanish, so the
localized solenoid admits no nontrivial torus input through that prime direction. -/
def xiCdimLocalizationSolenoidNoNontrivialTorusInput (S : Finset Nat) (d : Nat) : Prop :=
  ∀ p, p ∈ S → 2 ≤ p →
    ∀ φ : ℤ →+ (Fin d → ℤ),
      localizedSolenoidDualDivisibleAtPrime p (φ 1) →
      ∀ z : ℤ, φ z = 0

/-- Paper label: `thm:xi-cdim-localization-solenoid-no-nontrivial-torus-input`. -/
theorem paper_xi_cdim_localization_solenoid_no_nontrivial_torus_input
    (S : Finset Nat) (d : Nat) : xiCdimLocalizationSolenoidNoNontrivialTorusInput S d := by
  intro p hpS hp φ hdiv z
  have hone : φ 1 = 0 := vector_eq_zero_of_dvd_all_powers hp hdiv
  have hz : φ z = z • φ 1 := by
    simpa using φ.map_zsmul (1 : ℤ) z
  rw [hone] at hz
  simpa using hz

end Omega.Zeta
