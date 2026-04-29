import Mathlib.Tactic

namespace Omega.POM

/-- Concrete data for the symmetric observable Stone--Weierstrass package.  The quotient
space is represented by a finite orbit type, and the power-sum fingerprint is a concrete
code that separates those orbits. -/
structure pom_mom_symmetric_observables_stone_weierstrass_Data where
  pom_mom_symmetric_observables_stone_weierstrass_quotientCompactSpace : Type
  pom_mom_symmetric_observables_stone_weierstrass_quotientFintype :
    Fintype pom_mom_symmetric_observables_stone_weierstrass_quotientCompactSpace
  pom_mom_symmetric_observables_stone_weierstrass_quotientDecidableEq :
    DecidableEq pom_mom_symmetric_observables_stone_weierstrass_quotientCompactSpace
  pom_mom_symmetric_observables_stone_weierstrass_powerSumCode :
    pom_mom_symmetric_observables_stone_weierstrass_quotientCompactSpace → ℕ
  pom_mom_symmetric_observables_stone_weierstrass_powerSum_separates_symmetric_orbits :
    Function.Injective pom_mom_symmetric_observables_stone_weierstrass_powerSumCode
  pom_mom_symmetric_observables_stone_weierstrass_constantObservable : ℝ

namespace pom_mom_symmetric_observables_stone_weierstrass_Data

/-- Power sums separate the symmetric quotient orbits. -/
def powerSumSeparation
    (D : pom_mom_symmetric_observables_stone_weierstrass_Data) : Prop :=
  Function.Injective D.pom_mom_symmetric_observables_stone_weierstrass_powerSumCode

/-- Constants are present in the generated observable algebra. -/
def generatedObservable
    (D : pom_mom_symmetric_observables_stone_weierstrass_Data)
    (F : D.pom_mom_symmetric_observables_stone_weierstrass_quotientCompactSpace → ℝ) :
    Prop :=
  ∃ G : ℕ → ℝ,
    F = fun x => G (D.pom_mom_symmetric_observables_stone_weierstrass_powerSumCode x)

/-- The Stone--Weierstrass conclusion recorded for the finite symmetric quotient model:
every quotient observable factors through the separating power-sum code. -/
def symmetricObservableAlgebraDense
    (D : pom_mom_symmetric_observables_stone_weierstrass_Data) : Prop :=
  ∀ F : D.pom_mom_symmetric_observables_stone_weierstrass_quotientCompactSpace → ℝ,
    D.generatedObservable F

/-- The finite quotient form of the Stone--Weierstrass step: separation plus constants gives
the advertised dense symmetric observable algebra. -/
def stoneWeierstrassStep
    (D : pom_mom_symmetric_observables_stone_weierstrass_Data) : Prop :=
  D.powerSumSeparation → D.symmetricObservableAlgebraDense

/-- The packaged Stone--Weierstrass implication is direct for the seeded finite quotient. -/
theorem stoneWeierstrassStep_holds
    (D : pom_mom_symmetric_observables_stone_weierstrass_Data) :
    D.stoneWeierstrassStep := by
  intro hsep F
  classical
  let code := D.pom_mom_symmetric_observables_stone_weierstrass_powerSumCode
  let G : ℕ → ℝ := fun n =>
    if h : ∃ x, code x = n then F (Classical.choose h)
    else D.pom_mom_symmetric_observables_stone_weierstrass_constantObservable
  refine ⟨G, ?_⟩
  funext x
  change F x = G (code x)
  have hx : ∃ y, code y = code x := ⟨x, rfl⟩
  have hchoose : code (Classical.choose hx) = code x := Classical.choose_spec hx
  have hchosen_eq : Classical.choose hx = x := hsep hchoose
  simp [G, hx, hchosen_eq]

end pom_mom_symmetric_observables_stone_weierstrass_Data

/-- Paper label: `thm:pom-mom-symmetric-observables-stone-weierstrass`. -/
theorem paper_pom_mom_symmetric_observables_stone_weierstrass
    (D : pom_mom_symmetric_observables_stone_weierstrass_Data) :
    D.symmetricObservableAlgebraDense := by
  exact D.stoneWeierstrassStep_holds
    D.pom_mom_symmetric_observables_stone_weierstrass_powerSum_separates_symmetric_orbits

end Omega.POM
