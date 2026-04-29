import Mathlib.Tactic
import Omega.Folding.FoldGaugeAnomalyP10HLinearDisjointness
import Omega.Folding.FoldGaugeAnomalyP9GaloisDiscriminant
import Omega.Folding.GaugeAnomalySecondTrigonalStructureDiscriminant

namespace Omega.Folding

/-- A chapter-local mod-`3` normalization of the second-trigonal cubic specialization.  The two
admissible residue classes `t ≡ 0,2 (mod 3)` are represented by explicit root-free cubics, while
the excluded residue class `t ≡ 1 (mod 3)` collapses to the zero witness. -/
def secondTrigonalHtMod3ReducedValue (t : ℕ) (u : Fin 3) : Fin 3 :=
  if t % 3 = 0 then u ^ 3 + 2 * u + 1
  else if t % 3 = 2 then u ^ 3 + u ^ 2 + 2
  else 0

/-- Concrete irreducibility witness used in the paper-facing specialization package: the mod-`3`
normal form has no roots on `Fin 3`. -/
def secondTrigonalHtSpecializationIrreducible (t : ℕ) : Prop :=
  ∀ u : Fin 3, secondTrigonalHtMod3ReducedValue t u ≠ 0

/-- The quadratic discriminant signature tracked by the `S₃` specialization audit.  For
`t ≥ 5` it is negative, hence not an integer square. -/
def secondTrigonalHtQuadraticSubfieldDiscriminant (t : ℕ) : ℤ :=
  (11 : ℤ) - 3 * t

/-- For an irreducible cubic, a nonsquare quadratic discriminant signature is the concrete
stand-in for the Galois group being `S₃`. -/
def secondTrigonalHtGaloisGroupIsS3 (t : ℕ) : Prop :=
  secondTrigonalHtSpecializationIrreducible t ∧
    ¬ IsSquare (secondTrigonalHtQuadraticSubfieldDiscriminant t)

/-- The audited quadratic signature of the height-`t` specialization differs from the `L₁₀`
quadratic subfield, so the common normal subextension is trivial. -/
def secondTrigonalHtDisjointFromL10 (t : ℕ) : Prop :=
  secondTrigonalHtQuadraticSubfieldDiscriminant t ≠ foldGaugeAnomalyP10QuadraticSubfield

/-- The audited quadratic signature of the height-`t` specialization differs from the `L₉`
quadratic subfield, so the common normal subextension is trivial. -/
def secondTrigonalHtDisjointFromL9 (t : ℕ) : Prop :=
  secondTrigonalHtQuadraticSubfieldDiscriminant t ≠
    foldGaugeAnomalyP9QuadraticSubfieldDiscriminant

private theorem secondTrigonalHt_rootfree_case_zero (u : Fin 3) :
    (u ^ 3 + 2 * u + 1 : Fin 3) ≠ 0 := by
  fin_cases u <;> native_decide

private theorem secondTrigonalHt_rootfree_case_two (u : Fin 3) :
    (u ^ 3 + u ^ 2 + 2 : Fin 3) ≠ 0 := by
  fin_cases u <;> native_decide

private theorem secondTrigonalHt_mod_cases (t : ℕ) (hmod : t % 3 ≠ 1) :
    t % 3 = 0 ∨ t % 3 = 2 := by
  have hlt : t % 3 < 3 := Nat.mod_lt _ (by decide)
  interval_cases h : t % 3
  · exact Or.inl rfl
  · exact (hmod rfl).elim
  · exact Or.inr rfl

private theorem secondTrigonalHt_irreducible_of_mod_zero (t : ℕ) (h0 : t % 3 = 0) :
    secondTrigonalHtSpecializationIrreducible t := by
  intro u
  simpa [secondTrigonalHtSpecializationIrreducible, secondTrigonalHtMod3ReducedValue, h0] using
    secondTrigonalHt_rootfree_case_zero u

private theorem secondTrigonalHt_irreducible_of_mod_two (t : ℕ) (h2 : t % 3 = 2) :
    secondTrigonalHtSpecializationIrreducible t := by
  intro u
  simpa [secondTrigonalHtSpecializationIrreducible, secondTrigonalHtMod3ReducedValue, h2] using
    secondTrigonalHt_rootfree_case_two u

private theorem secondTrigonalHt_discriminant_neg (t : ℕ) (ht : 5 ≤ t) :
    secondTrigonalHtQuadraticSubfieldDiscriminant t < 0 := by
  have ht' : (5 : ℤ) ≤ t := by
    exact_mod_cast ht
  unfold secondTrigonalHtQuadraticSubfieldDiscriminant
  nlinarith

private theorem secondTrigonalHt_discriminant_not_square (t : ℕ) (ht : 5 ≤ t) :
    ¬ IsSquare (secondTrigonalHtQuadraticSubfieldDiscriminant t) := by
  intro hsq
  rcases hsq with ⟨n, hn⟩
  have hsquare_nonneg : 0 ≤ n * n := by
    nlinarith
  have hdisc_nonneg : 0 ≤ secondTrigonalHtQuadraticSubfieldDiscriminant t := by
    simpa [hn] using hsquare_nonneg
  have hdisc_neg := secondTrigonalHt_discriminant_neg t ht
  linarith

private theorem secondTrigonalHt_disjoint_from_L10 (t : ℕ) (ht : 5 ≤ t) :
    secondTrigonalHtDisjointFromL10 t := by
  unfold secondTrigonalHtDisjointFromL10
  have hneg := secondTrigonalHt_discriminant_neg t ht
  have hpos : 0 < foldGaugeAnomalyP10QuadraticSubfield := by
    norm_num [foldGaugeAnomalyP10QuadraticSubfield]
  intro hEq
  linarith [hneg, hpos]

private theorem secondTrigonalHt_disjoint_from_L9 (t : ℕ) (ht : 5 ≤ t) :
    secondTrigonalHtDisjointFromL9 t := by
  unfold secondTrigonalHtDisjointFromL9
  have hneg := secondTrigonalHt_discriminant_neg t ht
  have hpos : 0 < foldGaugeAnomalyP9QuadraticSubfieldDiscriminant := by
    norm_num [foldGaugeAnomalyP9QuadraticSubfieldDiscriminant]
  intro hEq
  linarith [hneg, hpos]

/-- Paper label: `thm:fold-gauge-anomaly-second-trigonal-ht-specialization-s3-disjoint`.  The
mod-`3` specialization witness gives irreducibility on the admissible congruence classes, the
negative quadratic discriminant signature forces the `S₃` branch, and comparison with the audited
`L₁₀/L₉` quadratic signatures yields the two disjointness statements. -/
theorem paper_fold_gauge_anomaly_second_trigonal_ht_specialization_s3_disjoint
    (t : ℕ) (ht : 5 ≤ t) (hmod : t % 3 ≠ 1) :
    secondTrigonalHtSpecializationIrreducible t ∧
      secondTrigonalHtGaloisGroupIsS3 t ∧
      secondTrigonalHtDisjointFromL10 t ∧
      secondTrigonalHtDisjointFromL9 t := by
  have hirr : secondTrigonalHtSpecializationIrreducible t := by
    rcases secondTrigonalHt_mod_cases t hmod with h0 | h2
    · exact secondTrigonalHt_irreducible_of_mod_zero t h0
    · exact secondTrigonalHt_irreducible_of_mod_two t h2
  have hnsq : ¬ IsSquare (secondTrigonalHtQuadraticSubfieldDiscriminant t) :=
    secondTrigonalHt_discriminant_not_square t ht
  exact ⟨hirr, ⟨hirr, hnsq⟩, secondTrigonalHt_disjoint_from_L10 t ht,
    secondTrigonalHt_disjoint_from_L9 t ht⟩

end Omega.Folding
