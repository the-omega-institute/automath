import Omega.Conclusion.FixedResolutionNontrivialCollisionMinimalCompleteStatistic

namespace Omega.Conclusion

open scoped BigOperators

/-- The exact finite signature records the atom location and multiplicity at fixed resolution. -/
def conclusion_r_atomic_spectrum_exact_signature_collapse_signature {r : ℕ}
    (delta mult : Fin r → ℕ) (i : Fin r) : ℕ × ℕ :=
  (delta i, mult i)

/-- A concrete shorter-prefix failure witness: the empty prefix cannot distinguish two labels. -/
def conclusion_r_atomic_spectrum_exact_signature_collapse_empty_prefix (_i : Fin 2) :
    Fin 0 → ℕ :=
  Fin.elim0

/-- The fixed-resolution exact-signature package used by the conclusion. -/
def conclusion_r_atomic_spectrum_exact_signature_collapse_statement {r : ℕ}
    (delta mult : Fin r → ℕ) : Prop :=
  NontrivialCollisionPrefixMinimallyComplete (fun q => ∑ i, mult i * delta i ^ q) ∧
    Function.Injective
      (conclusion_r_atomic_spectrum_exact_signature_collapse_signature delta mult) ∧
    ∃ x y : Fin 2,
      x ≠ y ∧
        conclusion_r_atomic_spectrum_exact_signature_collapse_empty_prefix x =
          conclusion_r_atomic_spectrum_exact_signature_collapse_empty_prefix y

/-- Paper label: `thm:conclusion-r-atomic-spectrum-exact-signature-collapse`. -/
theorem paper_conclusion_r_atomic_spectrum_exact_signature_collapse
    (r : ℕ) (delta mult : Fin r → ℕ) (hdelta : StrictMono delta)
    (hmult : ∀ i, 0 < mult i) :
    conclusion_r_atomic_spectrum_exact_signature_collapse_statement delta mult := by
  refine ⟨?_, ?_, ?_⟩
  · exact paper_conclusion_fixedresolution_nontrivial_collision_minimal_complete_statistic
      r delta mult hdelta hmult
  · intro i j hsig
    have hdelta_eq : delta i = delta j := congrArg Prod.fst hsig
    exact hdelta.injective hdelta_eq
  · refine ⟨0, 1, ?_, ?_⟩
    · decide
    · funext z
      exact Fin.elim0 z

end Omega.Conclusion
