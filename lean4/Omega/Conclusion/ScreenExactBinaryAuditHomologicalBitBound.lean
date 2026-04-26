import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Omega.SPG.RegisterLowerBound

namespace Omega.Conclusion

/-- Binary audit alphabet with `b` bits. -/
abbrev conclusion_screen_exact_binary_audit_homological_bit_bound_binary_audit_alphabet
    (b : ℕ) :=
  Fin b → Bool

/-- Paper label: `thm:conclusion-screen-exact-binary-audit-homological-bit-bound`.
If every screen fiber has cardinality `2^β`, then any audit that is injective on each fiber via
the joint map `(f_S, audit)` needs at least `b ≥ β` binary coordinates. Sharpness is realized by
an explicit injective encoding into `β` binary coordinates. -/
theorem paper_conclusion_screen_exact_binary_audit_homological_bit_bound
    {Ω Y : Type} [Fintype Ω] [DecidableEq Y]
    (fS : Ω → Y) (β b : ℕ)
    (audit :
      Ω →
        conclusion_screen_exact_binary_audit_homological_bit_bound_binary_audit_alphabet b)
    (ω0 : Ω)
    (hfiber :
      ∀ y : Set.range fS, Fintype.card {ω : Ω // fS ω = y.1} = 2 ^ β)
    (hinj : Function.Injective fun ω => (fS ω, audit ω)) :
    2 ^ β ≤ 2 ^ b ∧
      β ≤ b ∧
      ∃ sharp :
          Fin (2 ^ β) →
            conclusion_screen_exact_binary_audit_homological_bit_bound_binary_audit_alphabet β,
        Function.Injective sharp := by
  let y0 : Set.range fS := ⟨fS ω0, ω0, rfl⟩
  have hfiber_card :
      Fintype.card {ω : Ω // fS ω = fS ω0} = 2 ^ β := by
    simpa using hfiber y0
  have hregister :
      Fintype.card {ω : Ω // fS ω = fS ω0} ≤
        Fintype.card
          (conclusion_screen_exact_binary_audit_homological_bit_bound_binary_audit_alphabet b) :=
    by
      simpa using
        (Omega.SPG.RegisterLowerBound.paper_scan_projection_address_register_lower_bound
          (Ω := Ω)
          (Y := Y)
          (R := conclusion_screen_exact_binary_audit_homological_bit_bound_binary_audit_alphabet b)
          fS audit hinj (fS ω0))
  have hpow : 2 ^ β ≤ 2 ^ b := by
    simpa [hfiber_card,
      conclusion_screen_exact_binary_audit_homological_bit_bound_binary_audit_alphabet] using
      hregister
  have hbits : β ≤ b := by
    exact (Nat.pow_le_pow_iff_right (show 1 < 2 by decide)).1 hpow
  have hsharp_card :
      Fintype.card (Fin (2 ^ β)) ≤
        Fintype.card
          (conclusion_screen_exact_binary_audit_homological_bit_bound_binary_audit_alphabet β) := by
    simp [conclusion_screen_exact_binary_audit_homological_bit_bound_binary_audit_alphabet]
  rcases Function.Embedding.nonempty_of_card_le hsharp_card with ⟨sharp⟩
  exact ⟨hpow, hbits, sharp, sharp.injective⟩

end Omega.Conclusion
