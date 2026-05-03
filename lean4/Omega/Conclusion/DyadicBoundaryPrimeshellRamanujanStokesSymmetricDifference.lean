import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Conclusion

/-- Paper label:
`thm:conclusion-dyadic-boundary-primeshell-ramanujan-stokes-symmetric-difference`. -/
theorem paper_conclusion_dyadic_boundary_primeshell_ramanujan_stokes_symmetric_difference
    {ι : Type} [Fintype ι] (p C : ι → ℚ) (εU εV : ι → Bool)
    (scale area volGap : ℚ)
    (hRam : ∀ f, (if εU f = εV f then (0 : ℚ) else 1) = (1 + C f) / p f)
    (hArea : area = scale * ∑ f, (if εU f = εV f then (0 : ℚ) else 1))
    (hVol : volGap ≤ scale * ∑ f, (if εU f = εV f then (0 : ℚ) else 1)) :
    (∑ f, (if εU f = εV f then (0 : ℚ) else 1)) = ∑ f, (1 + C f) / p f ∧
      area = scale * ∑ f, (1 + C f) / p f ∧
        volGap ≤ scale * ∑ f, (1 + C f) / p f := by
  have hsum :
      (∑ f, (if εU f = εV f then (0 : ℚ) else 1)) = ∑ f, (1 + C f) / p f := by
    exact Finset.sum_congr rfl fun f _ => hRam f
  refine ⟨hsum, ?_, ?_⟩
  · rw [hArea, hsum]
  · simpa [hsum] using hVol

end Omega.Conclusion
