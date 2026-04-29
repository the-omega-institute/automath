import Mathlib.Combinatorics.Pigeonhole

/-- Fibers of a map out of a finite type are finite, without requiring decidable equality on
the codomain. -/
noncomputable instance xi_time_part79_window6_sector_19bit_collapse_fiber_fintype
    {A Sector : Type*} [Fintype A] (sigma : A → Sector) (s : Sector) :
    Fintype {a : A // sigma a = s} :=
  Fintype.ofFinite _

/-- A four-sector readout of a `2^21`-element finite set has a sector fiber of size at
least `2^19`. -/
theorem paper_xi_time_part79_window6_sector_19bit_collapse {A Sector : Type*} [Fintype A]
    [Fintype Sector] (sigma : A → Sector) (hA : Fintype.card A = 2 ^ 21)
    (hSector : Fintype.card Sector = 4) :
    ∃ s : Sector, 2 ^ 19 ≤ Fintype.card {a : A // sigma a = s} := by
  classical
  haveI : Nonempty Sector := by
    exact Fintype.card_pos_iff.mp (by rw [hSector]; norm_num)
  obtain ⟨s, hs⟩ :=
    Fintype.exists_le_card_fiber_of_mul_le_card (α := A) (β := Sector) (f := sigma)
      (n := 2 ^ 19) (by rw [hSector, hA]; norm_num)
  exact ⟨s, by simpa [Fintype.card_subtype] using hs⟩
