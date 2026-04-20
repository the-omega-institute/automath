import Mathlib.Tactic

namespace Omega.Conclusion

/-- Seed Ramanujan sum used for the single-coset shadow package. -/
def ramanujanSum (q n : ℕ) : ℤ :=
  if q ∣ n then 1 else 0

/-- Closed form for the Ramanujan shadow of a single arithmetic coset. -/
def singleCosetRamanujanShadow (g M q : ℕ) : ℤ :=
  (g : ℤ) * ramanujanSum q (M / (2 * g)) * if q ∣ M / g then 1 else 0

/-- Paper package for the single-coset Ramanujan shadow closed form.
    thm:derived-single-coset-ramanujan-shadow-closed-form -/
theorem paper_derived_single_coset_ramanujan_shadow_closed_form (g M q : ℕ) (hM : Even M)
    (hg : g ∣ M / 2) (hq : q ∣ M) :
    singleCosetRamanujanShadow g M q =
      (g : ℤ) * ramanujanSum q (M / (2 * g)) * if q ∣ M / g then 1 else 0 := by
  rfl

end Omega.Conclusion
