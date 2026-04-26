import Mathlib

namespace Omega.Zeta

/-- A concrete compositional `PW` model with additive composition law. -/
abbrev xi_time_central_extension_universal_pw := ℤ

/-- The raw time length carries a constant anomaly of size `1`. -/
def xi_time_central_extension_universal_length
    (w : xi_time_central_extension_universal_pw) : ℤ :=
  w + 1

/-- The length anomaly is the resulting constant `2`-cocycle. -/
def xi_time_central_extension_universal_length_cocycle
    (w₁ w₂ : xi_time_central_extension_universal_pw) : ℤ :=
  xi_time_central_extension_universal_length (w₁ + w₂) -
    xi_time_central_extension_universal_length w₁ -
      xi_time_central_extension_universal_length w₂

/-- The central extension adjoining an integer time register. -/
abbrev xi_time_central_extension_universal_extension :=
  xi_time_central_extension_universal_pw × ℤ

/-- The central extension multiplication corrected by the length cocycle. -/
def xi_time_central_extension_universal_mul
    (x y : xi_time_central_extension_universal_extension) :
    xi_time_central_extension_universal_extension :=
  (x.1 + y.1, x.2 + y.2 -
    xi_time_central_extension_universal_length_cocycle x.1 y.1)

/-- The lifted length on the central extension. -/
def xi_time_central_extension_universal_liftedLength
    (x : xi_time_central_extension_universal_extension) : ℤ :=
  xi_time_central_extension_universal_length x.1 + x.2

/-- A correction term exactly cancels the raw length anomaly. -/
def xi_time_central_extension_universal_compatibleCorrection
    (c : xi_time_central_extension_universal_pw → ℤ) : Prop :=
  ∀ w₁ w₂,
    c (w₁ + w₂) =
      c w₁ + c w₂ -
        xi_time_central_extension_universal_length_cocycle w₁ w₂

/-- The total strictly additive length obtained from a compatible correction. -/
def xi_time_central_extension_universal_totalLength
    (c : xi_time_central_extension_universal_pw → ℤ)
    (w : xi_time_central_extension_universal_pw) : ℤ :=
  xi_time_central_extension_universal_length w + c w

/-- The canonical lift of a compatible corrected length. -/
def xi_time_central_extension_universal_lift
    (c : xi_time_central_extension_universal_pw → ℤ)
    (w : xi_time_central_extension_universal_pw) :
    xi_time_central_extension_universal_extension :=
  (w, c w)

lemma xi_time_central_extension_universal_lift_mul
    (c : xi_time_central_extension_universal_pw → ℤ)
    (hc : xi_time_central_extension_universal_compatibleCorrection c)
    (w₁ w₂ : xi_time_central_extension_universal_pw) :
    xi_time_central_extension_universal_lift c (w₁ + w₂) =
      xi_time_central_extension_universal_mul
        (xi_time_central_extension_universal_lift c w₁)
        (xi_time_central_extension_universal_lift c w₂) := by
  ext
  · simp [xi_time_central_extension_universal_lift, xi_time_central_extension_universal_mul]
  · simpa [xi_time_central_extension_universal_lift, xi_time_central_extension_universal_mul] using
      hc w₁ w₂

/-- Paper label: `thm:xi-time-central-extension-universal`.
The cocycle-corrected central extension makes the lifted length strictly additive, and every
compatible corrected length on the base `PW` model factors through the canonical lift uniquely. -/
theorem paper_xi_time_central_extension_universal :
    (∀ x y : xi_time_central_extension_universal_extension,
      xi_time_central_extension_universal_liftedLength
          (xi_time_central_extension_universal_mul x y) =
        xi_time_central_extension_universal_liftedLength x +
          xi_time_central_extension_universal_liftedLength y) ∧
    ∀ c : xi_time_central_extension_universal_pw → ℤ,
      xi_time_central_extension_universal_compatibleCorrection c →
        ∃! F : xi_time_central_extension_universal_pw →
            xi_time_central_extension_universal_extension,
          (∀ w, (F w).1 = w) ∧
          (∀ w,
            xi_time_central_extension_universal_liftedLength (F w) =
              xi_time_central_extension_universal_totalLength c w) ∧
          ∀ w₁ w₂, F (w₁ + w₂) =
            xi_time_central_extension_universal_mul (F w₁) (F w₂) := by
  constructor
  · intro x y
    simp [xi_time_central_extension_universal_liftedLength,
      xi_time_central_extension_universal_mul,
      xi_time_central_extension_universal_length_cocycle,
      xi_time_central_extension_universal_length]
    ring
  · intro c hc
    refine ⟨xi_time_central_extension_universal_lift c, ?_, ?_⟩
    · constructor
      · intro w
        rfl
      · constructor
        · intro w
          simp [xi_time_central_extension_universal_liftedLength,
            xi_time_central_extension_universal_totalLength,
            xi_time_central_extension_universal_lift]
        · intro w₁ w₂
          exact xi_time_central_extension_universal_lift_mul c hc w₁ w₂
    · intro F hF
      funext w
      rcases hF with ⟨hproj, hlen, _hmul⟩
      have hk : (F w).2 = c w := by
        have hlen' := hlen w
        have hproj' := hproj w
        dsimp [xi_time_central_extension_universal_totalLength,
          xi_time_central_extension_universal_liftedLength,
          xi_time_central_extension_universal_length] at hlen'
        rw [hproj'] at hlen'
        linarith
      ext <;> simp [xi_time_central_extension_universal_lift, hproj w, hk]

end Omega.Zeta
