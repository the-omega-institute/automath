import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-time-part64a-minsector-pointwise-equivalence`. -/
theorem paper_xi_time_part64a_minsector_pointwise_equivalence {A B : Type*}
    [Fintype A] [Fintype B] (ι : A → B) (S : B → Prop) [DecidablePred S]
    (d : B → ℕ) (dmin fibHalf : ℕ) (hι : Function.Injective ι)
    (hcard : Fintype.card A = Fintype.card {b : B // S b})
    (hS : ∀ b, S b ↔ d b = dmin) (hd : dmin = fibHalf) :
    ((∀ b, S b ↔ ∃ a, ι a = b) ↔ ∀ a, d (ι a) = fibHalf) := by
  classical
  constructor
  · intro h a
    have hmem : S (ι a) := (h (ι a)).2 ⟨a, rfl⟩
    have hdeg : d (ι a) = dmin := (hS (ι a)).1 hmem
    simpa [hd] using hdeg
  · intro hdeg b
    constructor
    · intro hb
      let sectorMap : A → {b : B // S b} := fun a =>
        ⟨ι a, (hS (ι a)).2 (by
          calc
            d (ι a) = fibHalf := hdeg a
            _ = dmin := hd.symm)⟩
      have hsectorMap_inj : Function.Injective sectorMap := by
        intro a₁ a₂ hEq
        apply hι
        exact congrArg Subtype.val hEq
      have hsectorMap_bij : Function.Bijective sectorMap :=
        (Fintype.bijective_iff_injective_and_card sectorMap).2
          ⟨hsectorMap_inj, hcard⟩
      rcases hsectorMap_bij.2 ⟨b, hb⟩ with ⟨a, ha⟩
      exact ⟨a, congrArg Subtype.val ha⟩
    · rintro ⟨a, rfl⟩
      exact (hS (ι a)).2 (by simpa [hd] using hdeg a)

end Omega.Zeta
