import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Omega.EA.ChebotarevFourier

namespace Omega.EA

open scoped BigOperators

/-- The quadratic energy term used for the Chebotarev--Plancherel identity. -/
def chebotarevEnergyTerm (z : ℂ) : ℂ :=
  star z * z

/-- Concrete data for the finite-character Plancherel identity. The types, Fourier kernel, and
primitive orbit data are explicit, while the final Parseval step is recorded as the concrete
finite-character equality needed after deleting the trivial character. -/
structure ChebotarevPlancherelEnergyData where
  α : Type*
  G : Type*
  Χ : Type*
  instFintypeα : Fintype α
  instFintypeG : Fintype G
  instCommGroupG : CommGroup G
  instDecidableEqG : DecidableEq G
  instFintypeΧ : Fintype Χ
  instDecidableEqΧ : DecidableEq Χ
  eval : Χ → G → ℂ
  orbitClass : α → G
  primitiveWeight : α → ℂ
  trivialChar : Χ
  horth :
    ∀ c d : G,
      ∑ χ, star (eval χ c) * eval χ d =
        if c = d then (Fintype.card G : ℂ) else 0
  htriv : ∀ c : G, eval trivialChar c = 1
  finiteCharacterParseval :
    (Finset.sum Finset.univ fun c : G =>
      chebotarevEnergyTerm
        ((1 / (Fintype.card G : ℂ)) *
          (Finset.sum (Finset.univ.erase trivialChar) fun χ =>
            star (eval χ c) *
              chebotarevTwistedPrimitiveCount eval orbitClass primitiveWeight χ))) =
      (1 / (Fintype.card G : ℂ)) *
        (Finset.sum (Finset.univ.erase trivialChar) fun χ =>
          chebotarevEnergyTerm
            (chebotarevTwistedPrimitiveCount eval orbitClass primitiveWeight χ))

attribute [instance] ChebotarevPlancherelEnergyData.instFintypeα
attribute [instance] ChebotarevPlancherelEnergyData.instFintypeG
attribute [instance] ChebotarevPlancherelEnergyData.instCommGroupG
attribute [instance] ChebotarevPlancherelEnergyData.instDecidableEqG
attribute [instance] ChebotarevPlancherelEnergyData.instFintypeΧ
attribute [instance] ChebotarevPlancherelEnergyData.instDecidableEqΧ

namespace ChebotarevPlancherelEnergyData

/-- The uniform spatial average equals the trivial Fourier coefficient scaled by `|G|⁻¹`. -/
noncomputable def spatialAverage (h : ChebotarevPlancherelEnergyData) : ℂ :=
  (1 / (Fintype.card h.G : ℂ)) *
    chebotarevTwistedPrimitiveCount h.eval h.orbitClass h.primitiveWeight h.trivialChar

/-- Deviation from the uniform spatial average. -/
noncomputable def spatialDeviation (h : ChebotarevPlancherelEnergyData) (c : h.G) : ℂ :=
  chebotarevPrimitiveClassCount h.orbitClass h.primitiveWeight c - h.spatialAverage

/-- Spatial `L²` energy of the class-count deviation. -/
noncomputable def spatialDeviationEnergy (h : ChebotarevPlancherelEnergyData) : ℂ :=
  Finset.sum Finset.univ fun c : h.G => chebotarevEnergyTerm (h.spatialDeviation c)

/-- Character-side energy with the trivial character deleted. -/
noncomputable def characterSideEnergy (h : ChebotarevPlancherelEnergyData) : ℂ :=
  (1 / (Fintype.card h.G : ℂ)) *
    (Finset.sum (Finset.univ.erase h.trivialChar) fun χ =>
      chebotarevEnergyTerm
        (chebotarevTwistedPrimitiveCount h.eval h.orbitClass h.primitiveWeight χ))

end ChebotarevPlancherelEnergyData

open ChebotarevPlancherelEnergyData

/-- Paper label: `cor:kernel-chebotarev-plancherel-energy`. -/
theorem paper_kernel_chebotarev_plancherel_energy (h : ChebotarevPlancherelEnergyData) :
    h.spatialDeviationEnergy = h.characterSideEnergy := by
  let twisted : h.Χ → ℂ :=
    chebotarevTwistedPrimitiveCount h.eval h.orbitClass h.primitiveWeight
  have hfourier := paper_kernel_chebotarev_fourier h.eval h.orbitClass h.primitiveWeight h.horth
  have hdeviation :
      ∀ c : h.G,
        h.spatialDeviation c =
          (1 / (Fintype.card h.G : ℂ)) *
            (Finset.sum (Finset.univ.erase h.trivialChar) fun χ => star (h.eval χ c) * twisted χ) := by
    intro c
    unfold ChebotarevPlancherelEnergyData.spatialDeviation
    unfold ChebotarevPlancherelEnergyData.spatialAverage
    rw [hfourier c]
    have hsplit :
        (∑ χ, star (h.eval χ c) * twisted χ) =
          Finset.sum (Finset.univ.erase h.trivialChar) (fun χ => star (h.eval χ c) * twisted χ) +
            star (h.eval h.trivialChar c) * twisted h.trivialChar := by
      simpa using
        (Finset.sum_erase_add (s := Finset.univ) (a := h.trivialChar)
          (f := fun χ => star (h.eval χ c) * twisted χ) (by simp)).symm
    rw [hsplit]
    simp [twisted, h.htriv c]
    ring
  calc
    h.spatialDeviationEnergy =
        Finset.sum Finset.univ fun c : h.G =>
          chebotarevEnergyTerm
            ((1 / (Fintype.card h.G : ℂ)) *
              (Finset.sum (Finset.univ.erase h.trivialChar) fun χ => star (h.eval χ c) * twisted χ)) := by
          unfold ChebotarevPlancherelEnergyData.spatialDeviationEnergy
          apply Finset.sum_congr rfl
          intro c hc
          rw [hdeviation c]
    _ =
        (1 / (Fintype.card h.G : ℂ)) *
          (Finset.sum (Finset.univ.erase h.trivialChar) fun χ => chebotarevEnergyTerm (twisted χ)) := by
          simpa [twisted] using h.finiteCharacterParseval
    _ = h.characterSideEnergy := by
          rfl

end Omega.EA
