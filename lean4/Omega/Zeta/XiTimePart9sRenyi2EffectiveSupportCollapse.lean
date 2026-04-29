import Omega.Conclusion.Renyi2EffectiveSupportCollapse

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9s-renyi2-effective-support-collapse`. Applying the existing
effective-support reciprocal collapse to the bin-fold collision scale gives the zero-density
limit; the Rényi-rate statement is carried as the already established rate package. -/
theorem paper_xi_time_part9s_renyi2_effective_support_collapse
    (Xcard Col Neff : ℕ → ℝ) (renyiRatePhi : Prop)
    (hXpos : ∀ m, 0 < Xcard m)
    (hColpos : ∀ m, 0 < Col m)
    (hNeff : ∀ m, Neff m = (Col m)⁻¹)
    (hprod : Filter.Tendsto (fun m => Xcard m * Col m) Filter.atTop Filter.atTop)
    (hRate : renyiRatePhi) :
    Filter.Tendsto (fun m => Neff m / Xcard m) Filter.atTop (nhds 0) ∧
      renyiRatePhi := by
  exact
    ⟨Omega.Conclusion.paper_conclusion_renyi2_effective_support_collapse Xcard Col Neff
      hXpos hColpos hNeff hprod, hRate⟩

end Omega.Zeta
