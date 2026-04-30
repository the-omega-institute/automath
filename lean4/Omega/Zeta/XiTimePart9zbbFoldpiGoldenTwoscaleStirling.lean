import Omega.Zeta.XiTimePart9zbbFiniteStirlingSumTranslation

namespace Omega.Zeta

noncomputable section

/-- Paper label: `cor:xi-time-part9zbb-foldpi-golden-twoscale-stirling`. -/
theorem paper_xi_time_part9zbb_foldpi_golden_twoscale_stirling (R : ℕ) (κ : ℕ → ℂ)
    (φ : ℂ) :
    xi_time_part9zbb_finite_stirling_sum_translation_formal_odd_trunc R 2 κ
        (fun j : Fin 2 => if (j : ℕ) = 0 then φ⁻¹ else (φ ^ 2)⁻¹)
        (fun j : Fin 2 => if (j : ℕ) = 0 then 1 else φ) =
      xi_time_part9zbb_finite_stirling_sum_translation_stirling_trunc R 2 κ
        (fun j : Fin 2 => if (j : ℕ) = 0 then φ⁻¹ else (φ ^ 2)⁻¹)
        (fun j : Fin 2 => if (j : ℕ) = 0 then 1 else φ) := by
  simpa using
    paper_xi_time_part9zbb_finite_stirling_sum_translation R 2 κ
      (fun j : Fin 2 => if (j : ℕ) = 0 then φ⁻¹ else (φ ^ 2)⁻¹)
      (fun j : Fin 2 => if (j : ℕ) = 0 then 1 else φ)

end

end Omega.Zeta
