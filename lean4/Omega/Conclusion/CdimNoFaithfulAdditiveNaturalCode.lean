import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-cdim-no-faithful-additive-natural-code`. A faithful additive
natural-number code would force all finite-generated abelian-group classes to have support inside a
single finite set of primes, contradicting cyclic `p`-torsion classes for a prime outside it. -/
theorem paper_conclusion_cdim_no_faithful_additive_natural_code {IsoAbfg : Type*}
    [AddCommMonoid IsoAbfg] (torsionPrime : ℕ → IsoAbfg) (support : IsoAbfg → Finset ℕ)
    (hsupport_prime : ∀ p, Nat.Prime p → support (torsionPrime p) = {p})
    (hfinite_image_support :
      ∀ Φ : IsoAbfg → ℕ, Φ 0 = 0 → (∀ x y, Φ (x + y) = Φ x + Φ y) →
        Function.Injective Φ → ∃ S : Finset ℕ, ∀ x, support x ⊆ S)
    (hprime_avoid : ∀ S : Finset ℕ, ∃ p, Nat.Prime p ∧ p ∉ S) :
    ¬ ∃ Φ : IsoAbfg → ℕ,
      Φ 0 = 0 ∧ (∀ x y, Φ (x + y) = Φ x + Φ y) ∧ Function.Injective Φ := by
  rintro ⟨Φ, hzero, hadd, hinj⟩
  obtain ⟨S, hS⟩ := hfinite_image_support Φ hzero hadd hinj
  obtain ⟨p, hp, hp_not_mem⟩ := hprime_avoid S
  have hp_mem_support : p ∈ support (torsionPrime p) := by
    simp [hsupport_prime p hp]
  exact hp_not_mem (hS (torsionPrime p) hp_mem_support)

end Omega.Conclusion
