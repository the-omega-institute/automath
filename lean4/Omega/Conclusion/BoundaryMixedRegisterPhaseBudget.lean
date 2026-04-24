import Mathlib.Tactic

namespace Omega.Conclusion

/-- The `p`-adic depth-`ℓ` boundary source with `r` coordinates. -/
abbrev BoundaryMixedRegisterPhaseSource (p ell r : ℕ) := Fin (p ^ (ell * r))

/-- A discrete register bank carrying `B` binary bits. -/
abbrev BoundaryRegisterBank (B : ℕ) := Fin (2 ^ B)

/-- A `d`-tuple of `b`-bit phase coordinates. -/
abbrev BoundaryPhaseBank (d b : ℕ) := Fin d → Fin (2 ^ b)

/-- The explicit split encoding with `a` discrete `p`-adic coordinates and `r-a`
    phase coordinates at native spacing `p^{-ℓ}`. -/
abbrev BoundaryMixedSplitEncoding (p ell r a : ℕ) :=
  Fin (p ^ (ell * a)) × (Fin (r - a) → Fin (p ^ ell))

/-- The explicit split encoding has exactly the same cardinality as the boundary source. -/
theorem boundaryMixedSplitEncoding_card (p ell r a : ℕ) (ha : a ≤ r) :
    Fintype.card (BoundaryMixedSplitEncoding p ell r a) =
      Fintype.card (BoundaryMixedRegisterPhaseSource p ell r) := by
  have hsum : ell * a + ell * (r - a) = ell * r := by
    rw [← Nat.mul_add]
    simp [Nat.add_sub_of_le ha]
  calc
    Fintype.card (BoundaryMixedSplitEncoding p ell r a)
        = p ^ (ell * a) * (p ^ ell) ^ (r - a) := by
            simp [BoundaryMixedSplitEncoding, Fintype.card_prod, Fintype.card_fin]
    _ = p ^ (ell * a) * p ^ (ell * (r - a)) := by
          have hpow : (p ^ ell) ^ (r - a) = p ^ (ell * (r - a)) := by rw [pow_mul]
          rw [hpow]
    _ = p ^ (ell * a + ell * (r - a)) := by rw [← pow_add]
    _ = p ^ (ell * r) := by rw [hsum]
    _ = Fintype.card (BoundaryMixedRegisterPhaseSource p ell r) := by
          simp [BoundaryMixedRegisterPhaseSource, Fintype.card_fin]

/-- Paper-facing mixed budget law: any injective encoding into `B` binary register bits and
    `d` many `b`-bit phase coordinates satisfies the binary budget bound, and the split model
    with `a` discrete `p`-adic coordinates and `r-a` native phase coordinates is sharp.
    thm:conclusion-boundary-mixed-register-phase-budget -/
theorem paper_conclusion_boundary_mixed_register_phase_budget
    {p ell r B d b : ℕ}
    (hEnc :
      ∃ f : BoundaryMixedRegisterPhaseSource p ell r → BoundaryRegisterBank B × BoundaryPhaseBank d b,
        Function.Injective f) :
    Nat.clog 2 (p ^ (ell * r)) ≤ B + d * b ∧
      ∀ {a : ℕ}, a ≤ r →
        ∃ g : BoundaryMixedRegisterPhaseSource p ell r → BoundaryMixedSplitEncoding p ell r a,
          Function.Injective g := by
  refine ⟨?_, ?_⟩
  · rcases hEnc with ⟨f, hf⟩
    rw [Nat.clog_le_iff_le_pow (by omega)]
    calc
      p ^ (ell * r) = Fintype.card (BoundaryMixedRegisterPhaseSource p ell r) := by
        simp [BoundaryMixedRegisterPhaseSource, Fintype.card_fin]
      _ ≤ Fintype.card (BoundaryRegisterBank B × BoundaryPhaseBank d b) :=
        Fintype.card_le_of_injective f hf
      _ = 2 ^ B * (2 ^ b) ^ d := by
        simp [BoundaryRegisterBank, BoundaryPhaseBank, Fintype.card_prod, Fintype.card_fin]
      _ = 2 ^ B * 2 ^ (b * d) := by rw [pow_mul]
      _ = 2 ^ (B + b * d) := by rw [← pow_add]
      _ = 2 ^ (B + d * b) := by rw [Nat.mul_comm b d]
  · intro a ha
    classical
    let e : BoundaryMixedRegisterPhaseSource p ell r ≃ BoundaryMixedSplitEncoding p ell r a :=
      (Fintype.equivOfCardEq (boundaryMixedSplitEncoding_card p ell r a ha)).symm
    exact ⟨e, e.injective⟩

end Omega.Conclusion
