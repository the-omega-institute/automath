import Mathlib.Data.Finset.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete dual finite-generation package for prime-tail blindness.  The finitely many dual
generators model the image of `ℤ^d`; each generator carries an explicit finite prime support. -/
structure conclusion_boundary_prime_tail_blindness_Data where
  Prime : Type
  generatorRank : ℕ
  dualGenerator : Fin generatorRank → Prime → ℤ
  generatorSupport : Fin generatorRank → Finset Prime
  support_spec : ∀ i p, dualGenerator i p ≠ 0 → p ∈ generatorSupport i

namespace conclusion_boundary_prime_tail_blindness_Data

/-- The finite union of supports of the finitely many dual generators. -/
noncomputable def finitePrimeSupport (D : conclusion_boundary_prime_tail_blindness_Data) :
    Finset D.Prime := by
  classical
  exact Finset.univ.biUnion D.generatorSupport

/-- The phase channel factors through finitely many prime coordinates, expressed on the dual
generators: all nonzero generator coefficients lie in one finite prime set. -/
def hasFinitePrimeSupport (D : conclusion_boundary_prime_tail_blindness_Data) : Prop :=
  ∃ S : Finset D.Prime, ∀ i p, D.dualGenerator i p ≠ 0 → p ∈ S

end conclusion_boundary_prime_tail_blindness_Data

/-- Paper label: `thm:conclusion-boundary-prime-tail-blindness`. -/
theorem paper_conclusion_boundary_prime_tail_blindness
    (D : conclusion_boundary_prime_tail_blindness_Data) : D.hasFinitePrimeSupport := by
  classical
  refine ⟨D.finitePrimeSupport, ?_⟩
  intro i p hp
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, D.support_spec i p hp⟩

end Omega.Conclusion
