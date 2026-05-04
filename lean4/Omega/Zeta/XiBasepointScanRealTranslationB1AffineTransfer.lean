import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-basepoint-scan-real-translation-b1-affine-transfer`. -/
theorem paper_xi_basepoint_scan_real_translation_b1_affine_transfer (κ : ℕ)
    (critical : (Fin κ → ℝ) → (Fin κ → ℂ) → Prop) (X : Fin κ → ℝ) (p : Fin κ → ℂ)
    (t : ℝ) (A1 y1 b0 b1 : (Fin κ → ℂ) → ℝ) (hcrit : critical X p)
    (htranslate : ∀ (X : Fin κ → ℝ) (p : Fin κ → ℂ) (t : ℝ),
      critical X p → critical (fun i => X i + t) (fun i => p i + (t : ℂ)))
    (hb0 : ∀ p, b0 p = -((κ : ℝ) * ((κ : ℝ) + 1)))
    (hb1 : ∀ p, b1 p = -((κ : ℝ)^2) * A1 p + 2 * y1 p)
    (hA1 : ∀ (p : Fin κ → ℂ) (t : ℝ),
      A1 (fun i => p i + (t : ℂ)) = A1 p - 2 * (κ : ℝ) * t)
    (hy1 : ∀ (p : Fin κ → ℂ) (t : ℝ),
      y1 (fun i => p i + (t : ℂ)) = y1 p - (κ : ℝ) * t) :
    critical (fun i => X i + t) (fun i => p i + (t : ℂ)) ∧
      b0 (fun i => p i + (t : ℂ)) = b0 p ∧
        b1 (fun i => p i + (t : ℂ)) =
          b1 p + 2 * (κ : ℝ) * (((κ : ℝ)^2) - 1) * t ∧
          b1 (fun i => p i + (t : ℂ)) +
              (((κ : ℝ)^2) - 1) * A1 (fun i => p i + (t : ℂ)) =
            b1 p + (((κ : ℝ)^2) - 1) * A1 p := by
  refine ⟨htranslate X p t hcrit, ?_, ?_, ?_⟩
  · rw [hb0, hb0]
  · rw [hb1, hb1, hA1, hy1]
    ring
  · rw [hb1, hb1, hA1, hy1]
    ring

end Omega.Zeta
