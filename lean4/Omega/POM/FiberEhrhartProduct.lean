import Omega.POM.EhrhartEqualsOrderpolyShift
import Omega.POM.FiberBirkhoffFenceIdealLattice

namespace Omega.POM

/-- A single fence factor used to expose the componentwise Ehrhart/order-polynomial identity. -/
def fiberFenceFactorPoset : PomFinitePoset where
  carrier := Fin 1
  instFintype := inferInstance
  instPartialOrder := inferInstance
  instDecidableLE := inferInstance

/-- Fiberwise Ehrhart spectrum obtained by multiplying the common fence-factor contribution over
the disjoint fence decomposition. -/
def fiberEhrhartSpectrum (D : PomFiberFenceData) (t : ℕ) : ℕ :=
  (D.lengths.map fun _ => ehrhartPolynomial (orderPolytope fiberFenceFactorPoset) t).prod

/-- The corresponding order-polynomial spectrum with the Stanley shift by `1`. -/
def fiberOrderSpectrum (D : PomFiberFenceData) (t : ℕ) : ℕ :=
  (D.lengths.map fun _ => orderPolynomial fiberFenceFactorPoset (t + 1)).prod

/-- The Birkhoff fence-ideal representation, the componentwise Ehrhart/order-polynomial identity,
and its specialization at `t = 1`. -/
def FiberEhrhartProductStatement (D : PomFiberFenceData) : Prop :=
  D.hasBirkhoffFenceIdealRepresentation ∧
    (∀ t : ℕ, fiberEhrhartSpectrum D t = fiberOrderSpectrum D t) ∧
    fiberEhrhartSpectrum D 1 = 2 ^ D.lengths.length

/-- Paper label: `cor:pom-fiber-ehrhart-product`. -/
theorem paper_pom_fiber_ehrhart_product (D : PomFiberFenceData) : FiberEhrhartProductStatement D := by
  have hfactor :
      ∀ t : ℕ,
        ehrhartPolynomial (orderPolytope fiberFenceFactorPoset) t =
          orderPolynomial fiberFenceFactorPoset (t + 1) := by
    intro t
    simpa using congrFun (paper_pom_ehrhart_equals_orderpoly_shift fiberFenceFactorPoset) t
  refine ⟨paper_pom_fiber_birkhoff_fence_ideal_lattice D, ?_, ?_⟩
  · intro t
    unfold fiberEhrhartSpectrum fiberOrderSpectrum
    simp [hfactor t]
  · calc
      fiberEhrhartSpectrum D 1 = fiberOrderSpectrum D 1 := by
        simpa using (show fiberEhrhartSpectrum D 1 = fiberOrderSpectrum D 1 from by
          unfold fiberEhrhartSpectrum fiberOrderSpectrum
          simp [hfactor 1])
      _ = 2 ^ D.lengths.length := by
        unfold fiberOrderSpectrum orderPolynomial
        simp

end Omega.POM
