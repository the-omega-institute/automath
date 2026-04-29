import Omega.Zeta.XiTimePart9xaaLowfiberAnomalyTax

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9xaa-window6-audited-spectrum-exact-tax`. -/
theorem paper_xi_time_part9xaa_window6_audited_spectrum_exact_tax :
    Omega.Zeta.xi_time_part9xaa_lowfiber_anomaly_tax_statement (3, 21, 1, 8) ∧
      ((53 : Rat) / 1024 - (49 : Rat) / 1024 = 1 / 256) := by
  constructor
  · exact paper_xi_time_part9xaa_lowfiber_anomaly_tax (3, 21, 1, 8)
  · norm_num

end Omega.Zeta
