import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic

namespace Omega.Zeta

/-- The shifted Hankel matrix attached to the moment sequence. -/
def xi_time_part9zbj_shifted_spectral_zeta_hankel_localizing_hankel
    (M : ℕ → ℝ) (m ell : ℕ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
  fun i j => M (ell + i.1 + j.1)

/-- The shifted localizing matrix for the interval endpoint `rho`. -/
def xi_time_part9zbj_shifted_spectral_zeta_hankel_localizing_localizing
    (M : ℕ → ℝ) (rho : ℝ) (m ell : ℕ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
  fun i j => rho * M (ell + i.1 + j.1) - M (ell + i.1 + j.1 + 1)

/-- Paper label: `cor:xi-time-part9zbj-shifted-spectral-zeta-hankel-localizing`. -/
theorem paper_xi_time_part9zbj_shifted_spectral_zeta_hankel_localizing
    (M : ℕ → ℝ) (rho : ℝ)
    (hH : ∀ m ell : ℕ,
      Matrix.PosSemidef
        (xi_time_part9zbj_shifted_spectral_zeta_hankel_localizing_hankel M m ell))
    (hL : ∀ m ell : ℕ,
      Matrix.PosSemidef
        (xi_time_part9zbj_shifted_spectral_zeta_hankel_localizing_localizing M rho m ell)) :
    (∀ m ell : ℕ,
      Matrix.PosSemidef
        (xi_time_part9zbj_shifted_spectral_zeta_hankel_localizing_hankel M m ell) ∧
      Matrix.PosSemidef
        (xi_time_part9zbj_shifted_spectral_zeta_hankel_localizing_localizing M rho m ell)) ∧
      (∀ r : ℕ, 1 ≤ r → M r ^ 2 ≤ M (r - 1) * M (r + 1)) := by
  constructor
  · intro m ell
    exact ⟨hH m ell, hL m ell⟩
  · intro r hr
    have hdet :
        0 ≤
          Matrix.det
            (xi_time_part9zbj_shifted_spectral_zeta_hankel_localizing_hankel M 1 (r - 1)) :=
      (hH 1 (r - 1)).det_nonneg
    have hsub : r - 1 + 1 = r := Nat.sub_add_cancel hr
    have hsub_two : r - 1 + 1 + 1 = r + 1 := by omega
    have hminor : M r * M r ≤ M (r - 1) * M (r + 1) := by
      simpa [xi_time_part9zbj_shifted_spectral_zeta_hankel_localizing_hankel,
        Matrix.det_fin_two, hsub, hsub_two, Nat.add_assoc] using hdet
    simpa [pow_two] using hminor

end Omega.Zeta
