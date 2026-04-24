import Mathlib.Tactic
import Omega.Core.WalshFourier
import Omega.Core.WalshStokes
import Omega.Zeta.WalshParseval

namespace Omega.Zeta

open Omega.Core Finset
open scoped BigOperators

/-- Concrete two-cube observable whose Walsh coefficients are read off from boundary flux. -/
structure XiHypercubeLeyangStokesHolographyData where
  observable : Word 2 → ℤ

namespace XiHypercubeLeyangStokesHolographyData

/-- Directed-boundary flux across the face indexed by `I`. -/
def boundaryFlux (D : XiHypercubeLeyangStokesHolographyData) (I : Finset (Fin 2)) : ℤ :=
  Omega.Core.walshFlux I D.observable

/-- The Taylor/Walsh coefficient attached to `I`. -/
def taylorCoeff (D : XiHypercubeLeyangStokesHolographyData) (I : Finset (Fin 2)) : ℤ :=
  walshBias D.observable I

/-- The explicit Lee-Yang expansion on the two-cube. -/
def leeYangExpansion (f : Word 2 → ℤ) (z : ℤ) : ℤ :=
  ∑ I : Finset (Fin 2), walshBias f I * z ^ I.card

/-- Boundary flux determines every Walsh/Taylor coefficient on the two-cube. -/
def boundaryFluxDeterminesTaylorCoeffs (D : XiHypercubeLeyangStokesHolographyData) : Prop :=
  ∀ g : Word 2 → ℤ,
    (∀ I : Finset (Fin 2), D.boundaryFlux I = Omega.Core.walshFlux I g) →
      ∀ I : Finset (Fin 2), D.taylorCoeff I = walshBias g I

/-- Equality of all directed-boundary fluxes forces the same Lee-Yang zero set. -/
def boundaryFluxDeterminesLeeYangZeros (D : XiHypercubeLeyangStokesHolographyData) : Prop :=
  ∀ g : Word 2 → ℤ,
    (∀ I : Finset (Fin 2), D.boundaryFlux I = Omega.Core.walshFlux I g) →
      ∀ z : ℤ, leeYangExpansion D.observable z = 0 ↔ leeYangExpansion g z = 0

lemma walshChar_eq_activeBitSign (I : Finset (Fin 2)) (w : Word 2) :
    walshChar I w = (-1 : ℤ) ^ ((I.filter fun i => w i = true).card) := by
  classical
  induction I using Finset.induction_on with
  | empty =>
      simp [walshChar]
  | @insert i I hi ih =>
      by_cases hwi : w i = true
      · rw [walshChar_insert hi]
        simp [Finset.filter_insert, hi, hwi, ih, pow_succ, mul_comm]
      · rw [walshChar_insert hi]
        simp [Finset.filter_insert, hwi, ih]

lemma walshBias_eq_walshFlux (f : Word 2 → ℤ) (I : Finset (Fin 2)) :
    walshBias f I = Omega.Core.walshFlux I f := by
  rw [Omega.Core.walshStokes_finset]
  unfold walshBias
  refine Finset.sum_congr rfl ?_
  intro w hw
  rw [walshChar_eq_activeBitSign]

lemma boundaryFlux_eq_taylorCoeff (D : XiHypercubeLeyangStokesHolographyData) (I : Finset (Fin 2)) :
    D.boundaryFlux I = D.taylorCoeff I := by
  simpa [boundaryFlux, taylorCoeff] using (walshBias_eq_walshFlux D.observable I).symm

lemma boundaryFlux_parseval (D : XiHypercubeLeyangStokesHolographyData) :
    ∑ I : Finset (Fin 2), D.boundaryFlux I ^ 2 =
      (2 : ℤ) ^ 2 * ∑ w : Word 2, D.observable w ^ 2 := by
  simp_rw [boundaryFlux, ← walshBias_eq_walshFlux]
  simpa using
    Omega.Zeta.WalshParseval.parseval_general 2 D.observable

lemma boundaryFluxDeterminesTaylorCoeffs_holds (D : XiHypercubeLeyangStokesHolographyData) :
    D.boundaryFluxDeterminesTaylorCoeffs := by
  intro g hflux I
  calc
    D.taylorCoeff I = D.boundaryFlux I := by symm; exact D.boundaryFlux_eq_taylorCoeff I
    _ = Omega.Core.walshFlux I g := hflux I
    _ = walshBias g I := by simpa using (walshBias_eq_walshFlux g I).symm

lemma leeYangExpansion_congr {f g : Word 2 → ℤ}
    (hcoeff : ∀ I : Finset (Fin 2), walshBias f I = walshBias g I) :
    ∀ z : ℤ, leeYangExpansion f z = leeYangExpansion g z := by
  intro z
  unfold leeYangExpansion
  refine Finset.sum_congr rfl ?_
  intro I hI
  rw [hcoeff I]

lemma boundaryFluxDeterminesLeeYangZeros_holds (D : XiHypercubeLeyangStokesHolographyData) :
    D.boundaryFluxDeterminesLeeYangZeros := by
  intro g hflux z
  have hcoeff := D.boundaryFluxDeterminesTaylorCoeffs_holds g hflux
  have hexp : leeYangExpansion D.observable z = leeYangExpansion g z := by
    exact leeYangExpansion_congr hcoeff z
  rw [hexp]

end XiHypercubeLeyangStokesHolographyData

open XiHypercubeLeyangStokesHolographyData

/-- Paper label: `cor:xi-hypercube-leyang-stokes-holography`. Directed boundary flux equals the
Walsh coefficient family, and on the two-cube that coefficient family determines the explicit
Lee-Yang expansion and hence its zero set. -/
theorem paper_xi_hypercube_leyang_stokes_holography (D : XiHypercubeLeyangStokesHolographyData) :
    D.boundaryFluxDeterminesTaylorCoeffs ∧ D.boundaryFluxDeterminesLeeYangZeros := by
  exact ⟨D.boundaryFluxDeterminesTaylorCoeffs_holds, D.boundaryFluxDeterminesLeeYangZeros_holds⟩

end Omega.Zeta
