import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic

namespace Omega.Conclusion

/-- The three hidden-offset templates attached to multiplicities `d(w) = 2, 3, 4`. -/
def window6HiddenOffsets : ℕ → Finset ℕ
  | 2 => {0, 21}
  | 3 => {0, 21, 34}
  | 4 => {0, 21, 34, 55}
  | _ => ∅

/-- Ramanujan contribution of one hidden offset: the zero offset contributes `φ(q)`, while a
coprime nonzero offset contributes `μ(q)`. -/
def window6RamanujanTerm (q a : ℕ) : ℤ :=
  if a = 0 then Nat.totient q else if Nat.Coprime q a then ArithmeticFunction.moebius q else 0

/-- Average Ramanujan contribution over the hidden-offset template of size `d`. -/
def window6RamanujanMean (q d : ℕ) : ℚ :=
  (Finset.sum (window6HiddenOffsets d) fun a => (window6RamanujanTerm q a : ℚ)) /
    ((window6HiddenOffsets d).card : ℚ)

private lemma window6_coprime_21 {q : ℕ} (hq : Nat.Coprime q 39270) : Nat.Coprime q 21 :=
  Nat.Coprime.of_dvd_right (show 21 ∣ 39270 by decide) hq

private lemma window6_coprime_34 {q : ℕ} (hq : Nat.Coprime q 39270) : Nat.Coprime q 34 :=
  Nat.Coprime.of_dvd_right (show 34 ∣ 39270 by decide) hq

private lemma window6_coprime_55 {q : ℕ} (hq : Nat.Coprime q 39270) : Nat.Coprime q 55 :=
  Nat.Coprime.of_dvd_right (show 55 ∣ 39270 by decide) hq

/-- Paper-facing Ramanujan fault law for the three window-`6` hidden templates: under the
prime-goodness condition `(q, 39270) = 1`, the nonzero offsets `21`, `34`, and `55` are units
modulo `q`, so the three template means have the explicit `φ/μ` form and their average is the
corresponding average of those three closed forms. -/
theorem paper_conclusion_window6_hidden_template_primegood_ramanujan_faultlaw
    (q : ℕ) (hq : Nat.Coprime q 39270) :
    window6RamanujanMean q 2 =
        ((Nat.totient q : ℚ) + (ArithmeticFunction.moebius q : ℚ)) / 2 ∧
      window6RamanujanMean q 3 =
        ((Nat.totient q : ℚ) + 2 * (ArithmeticFunction.moebius q : ℚ)) / 3 ∧
      window6RamanujanMean q 4 =
        ((Nat.totient q : ℚ) + 3 * (ArithmeticFunction.moebius q : ℚ)) / 4 ∧
      (window6RamanujanMean q 2 + window6RamanujanMean q 3 + window6RamanujanMean q 4) / 3 =
        ((((Nat.totient q : ℚ) + (ArithmeticFunction.moebius q : ℚ)) / 2) +
          (((Nat.totient q : ℚ) + 2 * (ArithmeticFunction.moebius q : ℚ)) / 3) +
          (((Nat.totient q : ℚ) + 3 * (ArithmeticFunction.moebius q : ℚ)) / 4)) / 3 := by
  have h21 : Nat.Coprime q 21 := window6_coprime_21 hq
  have h34 : Nat.Coprime q 34 := window6_coprime_34 hq
  have h55 : Nat.Coprime q 55 := window6_coprime_55 hq
  have hg21 : q.gcd 21 = 1 := h21.gcd_eq_one
  have hg34 : q.gcd 34 = 1 := h34.gcd_eq_one
  have hg55 : q.gcd 55 = 1 := h55.gcd_eq_one
  have h2 :
      window6RamanujanMean q 2 =
        ((Nat.totient q : ℚ) + (ArithmeticFunction.moebius q : ℚ)) / 2 := by
    simp [window6RamanujanMean, window6HiddenOffsets, window6RamanujanTerm,
      Nat.coprime_iff_gcd_eq_one, hg21]
  have h3 :
      window6RamanujanMean q 3 =
        ((Nat.totient q : ℚ) + 2 * (ArithmeticFunction.moebius q : ℚ)) / 3 := by
    simp [window6RamanujanMean, window6HiddenOffsets, window6RamanujanTerm,
      Nat.coprime_iff_gcd_eq_one, hg21, hg34]
    ring
  have h4 :
      window6RamanujanMean q 4 =
        ((Nat.totient q : ℚ) + 3 * (ArithmeticFunction.moebius q : ℚ)) / 4 := by
    simp [window6RamanujanMean, window6HiddenOffsets, window6RamanujanTerm,
      Nat.coprime_iff_gcd_eq_one, hg21, hg34, hg55]
    ring
  refine ⟨h2, h3, h4, ?_⟩
  rw [h2, h3, h4]

end Omega.Conclusion
