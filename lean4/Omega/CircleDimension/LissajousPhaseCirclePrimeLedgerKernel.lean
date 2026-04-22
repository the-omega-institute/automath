import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

namespace Omega.CircleDimension

/-- The degree-`d` additive cover of the phase circle. -/
noncomputable def lissajousPhaseCover (d : ℕ) (t : ℝ) : ℝ :=
  (d : ℝ) * t

/-- The primitive phase lift attached to the coprime frequencies `(α, β)`. -/
noncomputable def primitiveLissajousPhaseLift (α β : ℕ) (t : ℝ) : ℝ × ℝ :=
  ((α : ℝ) * t, (β : ℝ) * t)

/-- Translation by the phase offset `δ` in the first coordinate. -/
noncomputable def lissajousPhaseTranslate (δ : ℝ) : ℝ × ℝ → ℝ × ℝ
  | (u, v) => (δ + u, v)

/-- The phase-space Lissajous lift before the Joukowsky gate. -/
noncomputable def lissajousPhaseLift (a b : ℕ) (δ t : ℝ) : ℝ × ℝ :=
  ((a : ℝ) * t + δ, (b : ℝ) * t)

/-- The coordinatewise Joukowsky projection in additive phase coordinates. -/
noncomputable def phaseJoukowskyPair : ℝ × ℝ → ℝ × ℝ
  | (u, v) => (Real.cos u, Real.cos v)

/-- The visible Lissajous orbit in the plane. -/
noncomputable def lissajousVisibleOrbit (a b : ℕ) (δ t : ℝ) : ℝ × ℝ :=
  (Real.cos ((a : ℝ) * t + δ), Real.cos ((b : ℝ) * t))

/-- All common frequency information is concentrated in the gcd. -/
def lissajousPrimeLedgerKernel (a b : ℕ) : ℕ :=
  Nat.gcd a b

/-- Paper label: `thm:cdim-lissajous-phase-circle-prime-ledger-kernel`. -/
theorem paper_cdim_lissajous_phase_circle_prime_ledger_kernel
    (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (δ : ℝ) :
    let d := lissajousPrimeLedgerKernel a b
    let α := a / d
    let β := b / d
    Nat.Coprime α β ∧
      d ∣ a ∧
      d ∣ b ∧
      (∀ t : ℝ,
        lissajousPhaseLift a b δ t =
          lissajousPhaseTranslate δ
            (primitiveLissajousPhaseLift α β (lissajousPhaseCover d t))) ∧
      (∀ t : ℝ, lissajousVisibleOrbit a b δ t =
        phaseJoukowskyPair (lissajousPhaseLift a b δ t)) ∧
      Fintype.card (Fin d) = d := by
  dsimp [lissajousPrimeLedgerKernel]
  refine ⟨?_, Nat.gcd_dvd_left a b, Nat.gcd_dvd_right a b, ?_, ?_, Fintype.card_fin _⟩
  · have hcop :
        Nat.Coprime (a / Nat.gcd a b) (b / Nat.gcd a b) :=
      Nat.gcd_div_gcd_div_gcd_of_pos_left (show 0 < a by omega)
    simpa using hcop
  · intro t
    ext <;> simp [lissajousPhaseLift, lissajousPhaseTranslate, primitiveLissajousPhaseLift,
      lissajousPhaseCover]
    · have hd : Nat.gcd a b ∣ a := Nat.gcd_dvd_left a b
      have hmul : ((a / Nat.gcd a b) * Nat.gcd a b : ℕ) = a := Nat.div_mul_cancel hd
      have hcast : (((a / Nat.gcd a b) * Nat.gcd a b : ℕ) : ℝ) = a := by exact_mod_cast hmul
      have hrhs :
          ((a / Nat.gcd a b : ℕ) : ℝ) * ((Nat.gcd a b : ℕ) : ℝ) * t =
            (((a / Nat.gcd a b) * Nat.gcd a b : ℕ) : ℝ) * t := by
        norm_num
      rw [← hcast]
      calc
        (((a / Nat.gcd a b) * Nat.gcd a b : ℕ) : ℝ) * t + δ
            = δ + (((a / Nat.gcd a b) * Nat.gcd a b : ℕ) : ℝ) * t := by ring
        _ = δ + ((a / Nat.gcd a b : ℕ) : ℝ) * ((Nat.gcd a b : ℕ) : ℝ) * t := by
          rw [hrhs]
        _ = δ + ((a / Nat.gcd a b : ℕ) : ℝ) * (((Nat.gcd a b : ℕ) : ℝ) * t) := by ring
    · have hd : Nat.gcd a b ∣ b := Nat.gcd_dvd_right a b
      have hmul : ((b / Nat.gcd a b) * Nat.gcd a b : ℕ) = b := Nat.div_mul_cancel hd
      have hcast : (((b / Nat.gcd a b) * Nat.gcd a b : ℕ) : ℝ) = b := by exact_mod_cast hmul
      have hrhs :
          ((b / Nat.gcd a b : ℕ) : ℝ) * ((Nat.gcd a b : ℕ) : ℝ) * t =
            (((b / Nat.gcd a b) * Nat.gcd a b : ℕ) : ℝ) * t := by
        norm_num
      rw [← hcast]
      calc
        (((b / Nat.gcd a b) * Nat.gcd a b : ℕ) : ℝ) * t
            = ((b / Nat.gcd a b : ℕ) : ℝ) * ((Nat.gcd a b : ℕ) : ℝ) * t := by
              rw [hrhs]
        _ = ((b / Nat.gcd a b : ℕ) : ℝ) * (((Nat.gcd a b : ℕ) : ℝ) * t) := by ring
  · intro t
    rfl

end Omega.CircleDimension
