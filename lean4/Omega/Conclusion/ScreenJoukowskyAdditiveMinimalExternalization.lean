import Omega.Conclusion.ScreenExactBinaryAuditHomologicalBitBound

namespace Omega.Conclusion

/-- Coordinatewise radial audit used for the additive externalization package. -/
def conclusion_screen_joukowsky_additive_minimal_externalization_radial_observable
    {k : ℕ} : (Fin k → ℕ) → Fin k → ℕ :=
  fun v => v

/-- The coordinatewise audit is decoded by the identity map. -/
def conclusion_screen_joukowsky_additive_minimal_externalization_radial_reconstruction
    {k : ℕ} : (Fin k → ℕ) → Fin k → ℕ :=
  fun obs => obs

/-- Paper label: `thm:conclusion-screen-joukowsky-additive-minimal-externalization`. The discrete
screen fiber already forces at least `β` binary audit bits, while the coordinatewise Joukowsky
radial package is sharp at exactly `k` extra scalar observables. -/
theorem paper_conclusion_screen_joukowsky_additive_minimal_externalization
    {Ω Y : Type} [Fintype Ω] [DecidableEq Y]
    (fS : Ω → Y) (ω0 : Ω) (β b k : ℕ)
    (audit :
      Ω →
        conclusion_screen_exact_binary_audit_homological_bit_bound_binary_audit_alphabet b)
    (hfiber :
      ∀ y : Set.range fS, Fintype.card {ω : Ω // fS ω = y.1} = 2 ^ β)
    (hinj : Function.Injective fun ω => (fS ω, audit ω))
    (radialProfile : Fin k → ℕ) :
    (2 ^ β ≤ 2 ^ b ∧
      β ≤ b ∧
      ∃ sharp :
          Fin (2 ^ β) →
            conclusion_screen_exact_binary_audit_homological_bit_bound_binary_audit_alphabet β,
        Function.Injective sharp) ∧
      (∀ d : ℕ, d < k → ¬ Fintype.card (Fin k) ≤ d) ∧
        k = Fintype.card (Fin k) ∧
        Function.LeftInverse
          (conclusion_screen_joukowsky_additive_minimal_externalization_radial_reconstruction
            (k := k))
          (conclusion_screen_joukowsky_additive_minimal_externalization_radial_observable
            (k := k)) ∧
        Function.Injective
          (conclusion_screen_joukowsky_additive_minimal_externalization_radial_observable
            (k := k)) := by
  let _ := radialProfile
  rcases
      paper_conclusion_screen_exact_binary_audit_homological_bit_bound
        fS β b audit ω0 hfiber hinj with
    ⟨hpow, hbits, sharp, hsharp⟩
  have hmin : ∀ d : ℕ, d < k → ¬ Fintype.card (Fin k) ≤ d := by
    intro d hd hcard
    have hk : k ≤ d := by
      simpa [Fintype.card_fin] using hcard
    exact Nat.not_le_of_lt hd hk
  have hleft :
      Function.LeftInverse
        (conclusion_screen_joukowsky_additive_minimal_externalization_radial_reconstruction
          (k := k))
        (conclusion_screen_joukowsky_additive_minimal_externalization_radial_observable
          (k := k)) := by
    intro v
    rfl
  have hinj_radial :
      Function.Injective
        (conclusion_screen_joukowsky_additive_minimal_externalization_radial_observable
          (k := k)) :=
    Function.LeftInverse.injective hleft
  exact ⟨⟨hpow, hbits, sharp, hsharp⟩, hmin, by simp [Fintype.card_fin], hleft, hinj_radial⟩

end Omega.Conclusion
