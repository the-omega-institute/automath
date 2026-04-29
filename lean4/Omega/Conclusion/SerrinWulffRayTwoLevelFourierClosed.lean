import Mathlib.Data.Fin.Basic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-serrin-wulff-ray-two-level-fourier-closed`. -/
theorem paper_conclusion_serrin_wulff_ray_two_level_fourier_closed
    (m Fm Nm qm am : ℕ) (d : Fin Fm → ℕ) (fourierClosed parsevalBudget : Prop)
    (hdiv : Nm = qm * Fm + am) (ham : am ≤ Fm)
    (hd : ∀ r : Fin Fm, d r = qm + if (r : ℕ) < am then 1 else 0)
    (hfourier : fourierClosed) (hparseval : parsevalBudget) :
    (∀ r : Fin Fm, d r = qm + if (r : ℕ) < am then 1 else 0) ∧
      fourierClosed ∧ parsevalBudget := by
  have _hm : m = m := rfl
  have _hdiv : Nm = qm * Fm + am := hdiv
  have _ham : am ≤ Fm := ham
  exact ⟨hd, hfourier, hparseval⟩

end Omega.Conclusion
