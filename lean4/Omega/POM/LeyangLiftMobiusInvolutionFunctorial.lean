import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic

namespace Omega.POM

open Polynomial

/-- A simple Lee--Yang lift obtained by substituting the odd monomial `u ↦ u^3`. -/
noncomputable def leyangLift (P : Polynomial ℤ) : Polynomial ℤ :=
  P.comp ((X : Polynomial ℤ) ^ 3)

/-- The Möbius involution is modelled by the sign-flip substitution `u ↦ -u`. -/
noncomputable def mobiusInvolution (P : Polynomial ℤ) : Polynomial ℤ :=
  P.comp (-(X : Polynomial ℤ))

lemma leyangLift_mobius_exchange (P : Polynomial ℤ) :
    leyangLift (mobiusInvolution P) = mobiusInvolution (leyangLift P) := by
  calc
    leyangLift (mobiusInvolution P)
        = P.comp ((-(X : Polynomial ℤ)).comp ((X : Polynomial ℤ) ^ 3)) := by
            simp [leyangLift, mobiusInvolution, Polynomial.comp_assoc]
    _ = P.comp (((X : Polynomial ℤ) ^ 3).comp (-(X : Polynomial ℤ))) := by
          congr 1
          simp [pow_succ, mul_comm]
    _ = mobiusInvolution (leyangLift P) := by
          simp [leyangLift, mobiusInvolution, Polynomial.comp_assoc]

lemma mobiusInvolution_involutive (P : Polynomial ℤ) :
    mobiusInvolution (mobiusInvolution P) = P := by
  rw [mobiusInvolution, mobiusInvolution, Polynomial.comp_assoc]
  simp

/-- Chapter-local witness for the Lee--Yang lift / Möbius involution package. The data record a
Lee--Yang family of polynomials, a seed polynomial in that family, and closure under the two
substitution functors. -/
structure LeyangLiftMobiusInvolutionFunctorialData where
  leeYangFamily : Set (Polynomial ℤ)
  seed : Polynomial ℤ
  seed_mem : seed ∈ leeYangFamily
  closedUnderMobius :
    ∀ {P : Polynomial ℤ}, P ∈ leeYangFamily → mobiusInvolution P ∈ leeYangFamily
  closedUnderLift :
    ∀ {P : Polynomial ℤ}, P ∈ leeYangFamily → leyangLift P ∈ leeYangFamily

/-- The Lee--Yang lift and the Möbius involution commute on the distinguished seed polynomial. -/
def LeyangLiftMobiusInvolutionFunctorialData.exchangeLaw
    (D : LeyangLiftMobiusInvolutionFunctorialData) : Prop :=
  leyangLift (mobiusInvolution D.seed) = mobiusInvolution (leyangLift D.seed)

/-- Applying the Möbius involution twice returns the seed polynomial. -/
def LeyangLiftMobiusInvolutionFunctorialData.involutionLaw
    (D : LeyangLiftMobiusInvolutionFunctorialData) : Prop :=
  mobiusInvolution (mobiusInvolution D.seed) = D.seed

/-- The lifted Möbius transform stays inside the Lee--Yang family. -/
def LeyangLiftMobiusInvolutionFunctorialData.leeYangPreservation
    (D : LeyangLiftMobiusInvolutionFunctorialData) : Prop :=
  mobiusInvolution (leyangLift D.seed) ∈ D.leeYangFamily

/-- Paper-facing Lee--Yang lift / Möbius involution package.
    thm:pom-leyang-lift-mobius-involution-functorial -/
theorem paper_pom_leyang_lift_mobius_involution_functorial
    (D : LeyangLiftMobiusInvolutionFunctorialData) :
    D.exchangeLaw ∧ D.involutionLaw ∧ D.leeYangPreservation := by
  have hExchange : D.exchangeLaw := by
    simpa [LeyangLiftMobiusInvolutionFunctorialData.exchangeLaw] using
      leyangLift_mobius_exchange D.seed
  have hInvolution : D.involutionLaw := by
    simpa [LeyangLiftMobiusInvolutionFunctorialData.involutionLaw] using
      mobiusInvolution_involutive D.seed
  have hMobiusSeed : mobiusInvolution D.seed ∈ D.leeYangFamily :=
    D.closedUnderMobius D.seed_mem
  have hLiftedMobius : leyangLift (mobiusInvolution D.seed) ∈ D.leeYangFamily :=
    D.closedUnderLift hMobiusSeed
  have hPreservation : D.leeYangPreservation := by
    rw [LeyangLiftMobiusInvolutionFunctorialData.leeYangPreservation, ← hExchange]
    exact hLiftedMobius
  exact ⟨hExchange, hInvolution, hPreservation⟩

end Omega.POM
