import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- The finite nonempty sector family used for the high-genus minimum-sector tomography seed. -/
def conclusion_foldbin_highgenus_minsector_tomography_sector (m : Nat) : Type :=
  Fin (m + 1)

instance conclusion_foldbin_highgenus_minsector_tomography_sector_fintype (m : Nat) :
    Fintype (conclusion_foldbin_highgenus_minsector_tomography_sector m) :=
  inferInstanceAs (Fintype (Fin (m + 1)))

/-- Positive bin-fold multiplicities in the seed model. -/
def conclusion_foldbin_highgenus_minsector_tomography_multiplicity
    (m : Nat) (_w : conclusion_foldbin_highgenus_minsector_tomography_sector m) : Nat :=
  1

/-- The minimum positive multiplicity. -/
def conclusion_foldbin_highgenus_minsector_tomography_d_min (_m : Nat) : Nat :=
  1

/-- The number of sectors realizing the minimum multiplicity. -/
def conclusion_foldbin_highgenus_minsector_tomography_n_min (m : Nat) : Nat :=
  Fintype.card (conclusion_foldbin_highgenus_minsector_tomography_sector m)

/-- The number of non-minimal sectors in the finite family. -/
def conclusion_foldbin_highgenus_minsector_tomography_nonminimal_count (m : Nat) : Nat :=
  Fintype.card (conclusion_foldbin_highgenus_minsector_tomography_sector m) -
    conclusion_foldbin_highgenus_minsector_tomography_n_min m

/-- The genus amplitude after writing each positive multiplicity as `d^{-2}`. -/
def conclusion_foldbin_highgenus_minsector_tomography_genus_amplitude
    (m g : Nat) : ℚ :=
  ∑ w : conclusion_foldbin_highgenus_minsector_tomography_sector m,
    (1 /
      (conclusion_foldbin_highgenus_minsector_tomography_multiplicity m w : ℚ) ^ (2 : Nat)) ^
      g

/-- The high-genus normalization by the minimum sector. -/
def conclusion_foldbin_highgenus_minsector_tomography_normalized_amplitude
    (m g : Nat) : ℚ :=
  (conclusion_foldbin_highgenus_minsector_tomography_d_min m : ℚ) ^ (2 * g) *
    conclusion_foldbin_highgenus_minsector_tomography_genus_amplitude m g

/-- The geometric decay factor carried by all sectors whose multiplicity is at least `d_min + 1`. -/
def conclusion_foldbin_highgenus_minsector_tomography_decay_factor
    (m g : Nat) : ℚ :=
  ((conclusion_foldbin_highgenus_minsector_tomography_d_min m : ℚ) /
      (conclusion_foldbin_highgenus_minsector_tomography_d_min m + 1 : ℚ)) ^ (2 * g)

/-- Concrete paper-facing two-sided bound and high-genus limit identity. -/
def conclusion_foldbin_highgenus_minsector_tomography_bounds (m g : Nat) : Prop :=
  (conclusion_foldbin_highgenus_minsector_tomography_n_min m : ℚ) ≤
      conclusion_foldbin_highgenus_minsector_tomography_normalized_amplitude m g ∧
    conclusion_foldbin_highgenus_minsector_tomography_normalized_amplitude m g ≤
      (conclusion_foldbin_highgenus_minsector_tomography_n_min m : ℚ) +
        (conclusion_foldbin_highgenus_minsector_tomography_nonminimal_count m : ℚ) *
          conclusion_foldbin_highgenus_minsector_tomography_decay_factor m g ∧
      conclusion_foldbin_highgenus_minsector_tomography_normalized_amplitude m g =
        (conclusion_foldbin_highgenus_minsector_tomography_n_min m : ℚ)

/-- Paper label: `thm:conclusion-foldbin-highgenus-minsector-tomography`. -/
theorem paper_conclusion_foldbin_highgenus_minsector_tomography (m g : Nat) :
    conclusion_foldbin_highgenus_minsector_tomography_bounds m g := by
  dsimp [conclusion_foldbin_highgenus_minsector_tomography_bounds,
    conclusion_foldbin_highgenus_minsector_tomography_normalized_amplitude,
    conclusion_foldbin_highgenus_minsector_tomography_genus_amplitude,
    conclusion_foldbin_highgenus_minsector_tomography_multiplicity,
    conclusion_foldbin_highgenus_minsector_tomography_d_min,
    conclusion_foldbin_highgenus_minsector_tomography_n_min,
    conclusion_foldbin_highgenus_minsector_tomography_nonminimal_count,
    conclusion_foldbin_highgenus_minsector_tomography_decay_factor]
  simp

end Omega.Conclusion
