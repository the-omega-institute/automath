import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-window6-hidden-chiral-band-invisible`. -/
theorem paper_conclusion_window6_hidden_chiral_band_invisible {V : Type} [AddCommGroup V]
    (inner : V → V → ℂ) (sigma : V → V)
    (hneg : ∀ g v, inner g (-v) = -inner g v)
    (hunitary : ∀ g v, inner (sigma g) (sigma v) = inner g v)
    (g v : V) (hg : sigma g = g) (hv : sigma v = -v) :
    inner g v = 0 := by
  have hunit : inner g (-v) = inner g v := by
    simpa [hg, hv] using hunitary g v
  have hcancel : inner g v = -inner g v :=
    hunit.symm.trans (hneg g v)
  have htwo : (2 : ℂ) * inner g v = 0 := by
    linear_combination hcancel
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

end Omega.Conclusion
